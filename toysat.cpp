#include "parser.h"

#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <stack>
#include <set>
#include <list>
#include <utility>
#include <string>
#include <iterator>
#include <algorithm>
#include <limits>
#include <chrono>
#include <cstdlib>
#include <ctime>
#include <cmath>
#include <cassert>


using namespace std;


//============================================================================//
//
//  Structs
//
//============================================================================//


struct Variable
{
  int value = 0;  // 0: Unassigned.  -1: Assigned False.  1: Assigned True.

  int reason = 0;  // 0: Not an implied variable.  ow: Index of reason clause.

  int decision_lvl = -1;  // -1: Unassinged.  0: Fixed.  ow: Decision lvl.

  double vsids_score = 0.0; // VSIDS heuristic score.

  int last_assignment = 0; // 0: Never assigned yet.  -1: False.  1: True.

  list< pair<int, int> > positive_watchlist;
    // Indices of clauses watching positive literal of this variable.
    // At which position: 0 or 1.

  list< pair<int, int> > negative_watchlist;
    // Indices of clauses watching negative literal of this variable.
    // At which position: 0 or 1.

  Variable() = default;

  ~Variable() = default;
};


struct Clause
{
  vector<int> literals;  // Watched: literals[0] and literals[1]

  // bool is_learned = false;  // doesn't seem useful?

  int implication = 0;  // bad implementation, used only in learned clause

  int lbd = 0;  // literals blocks distance

  double vsids_score = 0.0;  // VSIDS heuristic score for clause.

  Clause() = default;

  ~Clause() = default;

  int size() const { return literals.size(); }

  void push_back( int lit ) { literals.push_back( lit ); }

  void clear()
  {
    literals.clear();
    // is_learned = false;
    implication = 0;
    lbd = 0;
    vsids_score = 0.0;
  }

  int& operator[]( int i ) { return literals[i]; }
};


struct Bounded_queue
{
  queue<int> elements;

  int max_size = 1;

  int curr_size = 0;

  int sum = 0;

  Bounded_queue() = default;

  Bounded_queue( int max_sz ) : max_size(max_sz) {}

  ~Bounded_queue() = default;

  void push( int new_element )
  {
    if( curr_size < max_size ){
      ++curr_size;
    }else{
      sum -= elements.front();
      elements.pop();
    }
    elements.push( new_element );
    sum += new_element;
  }

  void pop()
  {
    if( curr_size > 0 ){
      sum -= elements.front();
      elements.pop();
      --curr_size;
    }
  }

  void resize( int new_max_sz ) { max_size = new_max_sz; }

  void clear()
  {
    elements = queue<int>();
    curr_size = 0;
    sum = 0;
  }

  bool is_full() const { return curr_size == max_size; }

  double average() const {
    if( curr_size == 0 ){
      return 0.0;
    }
    return static_cast<double>(sum) / curr_size;
  }

};



//============================================================================//
//
//  Global variables
//
//============================================================================//

const int X = 50;
  // At least X conflicts before restarting.
  // Smaller X stimulates restart tendency.

const double K = 0.8;
  // Restart when recent LBD average > 1/K * total LBD average of this pass.
  // Larger K suppresses restart tendency.

const int Y = 5000;
  // Keep track of Y "assignment stack sizes on conflict".

const double R = 1.4;
  // Postpone restart if assignment stack size on this conflict > R * average.

const double variable_vsids_decay = 0.95;

const double clause_vsids_decay = 0.999;

vector<vector<int>> raw_clauses;

vector<Clause> clauses;

vector<Variable> variables;

stack<int> assign_stack;

queue<int> bcp_queue;

Bounded_queue learned_lbd_queue(X);

Bounded_queue assign_stack_size_queue(Y);

Clause learned_clause;

bool conflict_on_fixed_variables = false;

int numof_variables = 0;

int initial_numof_clauses = 0;

int numof_learned_clauses = 0;

int curr_decision_lvl = 0;

int total_numof_conflicts = 0;  // Total number of conflicts occurred.

int numof_conflicts = 0;  // Number of conflicts occurred in this pass.

int numof_restarts = 0;  // Total number of restarts occurred.

int learned_lbd_sum = 0;  // Sum of LBDs of all learned clauses in this pass.

int sat_sentinel = 1;

double variable_vsids_inc = 1.0;

double clause_vsids_inc = 1.0;



//============================================================================//
//
//  Literal / Variable Operations
//
//============================================================================//


bool is_fixed_lit( int lit )
{
  return ( variables[abs(lit)].decision_lvl == 0 );
}


bool is_fixed_var( int var )
{
  return ( variables[var].decision_lvl == 0 );
}


bool is_assigned_lit( int lit )
{
  return ( variables[abs(lit)].value != 0 );
}


bool is_assigned_var( int var )
{
  return ( variables[var].value != 0 );
}


bool is_decided_var( int var )
{
  return ( variables[var].reason == 0 && variables[var].decision_lvl > 0 );
}


bool same_var( int lit1, int lit2 )
{
  return abs(lit1) == abs(lit2);
}


bool same_sign( int m, int n )
{
  return (m < 0) == (n < 0);
}


bool is_assigned_false( int lit )
{
  return ( is_assigned_lit(lit) && !same_sign(lit, variables[abs(lit)].value) );
}


bool preassign( int lit )
{
  int var = abs(lit);
  if( is_fixed_var(var) ){
    return false;
  }

  variables[var].value = (lit > 0) ? 1 : -1;
  variables[var].reason = 0;
  variables[var].decision_lvl = 0;

  return true;
}


bool assign( int lit, int d_lvl )
{
  int var = abs(lit);
  if( is_fixed_var(var) ){
    return false;
  }

  variables[var].value = (lit > 0) ? 1 : -1;
  variables[var].decision_lvl = d_lvl;
  variables[var].last_assignment = variables[var].value;

  if( d_lvl > 0 ){
    assign_stack.push(var);
  }

  return true;
}


bool deassign( int lit )
{
  int var = abs(lit);
  if( is_fixed_var(var) ){
    return false;
  }

  variables[var].value = 0;
  variables[var].reason = 0;
  variables[var].decision_lvl = -1;

  return true;
}


void watchlist_add( int lit, int cls, int w_order )
{
  if( lit < 0 ){
    variables[-lit].negative_watchlist.push_back( make_pair(cls, w_order) );
  }else{
    variables[lit].positive_watchlist.push_back( make_pair(cls, w_order) );
  }
}



//============================================================================//
//
//  Heuristic maintenance
//
//============================================================================//


void decay_variable_vsids()
{
  variable_vsids_inc *= (1 / variable_vsids_decay);
}


void decay_clause_vsids()
{
  clause_vsids_inc *= (1 / clause_vsids_decay);
}


void bump_variable_vsids( int var )
{
  if( (variables[var].vsids_score += variable_vsids_inc) > 1e100 ){
    for( int i = 1; i < variables.size(); ++i ){
      variables[i].vsids_score *= 1e-100;
    }
    variable_vsids_inc *= 1e-100;
  }
}


void bump_clause_vsids( int cls )
{
  if( (clauses[cls].vsids_score += clause_vsids_inc) > 1e20 ){
    for( int i = 1; i < clauses.size(); ++i ){
      clauses[i].vsids_score *= 1e-20;
    }
    clause_vsids_inc *= 1e-20;
  }
}



//============================================================================//
//
//  Preprocess Functions
//
//============================================================================//


void initialize_variables()
{
  variables.resize( numof_variables + 1 );
}


void initialize_clauses()
{
  clauses.resize( raw_clauses.size() + 1 );

  for( int i = 0; i < raw_clauses.size(); ++i ){
    clauses[i+1].literals = raw_clauses[i];
    watchlist_add( raw_clauses[i][0], i+1, 0 );
    watchlist_add( raw_clauses[i][1], i+1, 1 );

    for( int j = 0; j < raw_clauses[i].size(); ++j ){
      bump_variable_vsids( abs(raw_clauses[i][j]) );
    }
  }
}


void remove_duplicate_lit( vector<int>& v ){
  sort( v.begin(), v.end() );
  v.erase( unique( v.begin(), v.end() ), v.end() );
}


// Finds and deletes 1 single-literal clause.
// And returns the fixed literal in deleted clause.
// Returns 0 if no single-variable clause found.
int lit_in_1lit_clause()
{
  int fixed_lit = 0;
  for( auto cl = raw_clauses.begin(); cl != raw_clauses.end(); ++cl ){
    if( cl->size() == 1 ){
      fixed_lit = (*cl)[0];
      raw_clauses.erase(cl);
      return fixed_lit;
    }
  }
  return 0;
}


// Remove any occurrence of a fixed variable in the clauses.
// TRUE occurrence: Clause already satisfied. Remove the clause.
// False occurrence: If not alone in a clause, remove the literal.
//                   If alone in a clause, let next search find UNSAT.
void remove_fixed_lit(int lit)
{
  for( int i = 0; i < raw_clauses.size(); ++i ){
    for( int j = 0; j < raw_clauses[i].size(); ++j ){
      if( same_var(raw_clauses[i][j], lit) ){
        if( same_sign(raw_clauses[i][j], lit) ){
          raw_clauses.erase(raw_clauses.begin()+i);
          --i;
            // Without this, increment at end of for loop would miss a clause.
          break;
            // Jump to next clause.
        }else if( raw_clauses[i].size() > 1 ){
          raw_clauses[i].erase(raw_clauses[i].begin()+j);
        }
      }
    }
  }
}


// Remove any clause with only one literal.
// Literals in such clauses are made fixed.
// If contradicting fixed assignments are found, the problem is UNSAT.
bool deal_with_1lit_clauses()
{
  int fixed_lit = lit_in_1lit_clause();
  while( fixed_lit != 0 ){
    if( !preassign(fixed_lit) ){
      return false;
    }
    remove_fixed_lit(fixed_lit);

    fixed_lit = lit_in_1lit_clause();
  }

  return true;
}



//============================================================================//
//
//  BCP
//  Does BCP for each BCP source in the queue.
//  UNTIL: Conflict, OR the queue is empty.
//  only assigned (but possibly fixed) variable should be propagate source!!!!!
//  3 possible cases during BCP:
//    1)A new watched position (unassigned or assigned True) is found.
//      Update watchlists; delete old variable watchlist entry.
//    2)New watched not found and the other watched literal is unassigned:
//      This unassigned literal is implied: it must evaluate to True.
//    3)New watched not found and the other watched literal evaluates to False:
//      Conflict is found in this clause. Analysis will start on this clause.
//
//============================================================================//


bool new_watched( int cls, int w_psn )
{
  if( clauses[cls].size() <= 2 ){
    return false;
  }

  for( int i = 2; i < clauses[cls].size(); ++i ){
    if( !is_assigned_false(clauses[cls][i]) ){
      swap( clauses[cls][w_psn], clauses[cls][i] );
      return true;
    }
  }

  return false;
}


bool propagate(list< pair<int, int> > & w_list)
{
  int cls = 0;
  int w_order = 0;
  int other_w_lit = 0;

  for( auto w = w_list.begin(); w != w_list.end(); ){
    cls = w->first;
    w_order = w->second;

    if( !new_watched( cls, w_order ) ){  // New watched literal not found.
      other_w_lit = clauses[cls][1 - w_order];

      if( is_assigned_false(other_w_lit) ){  // Conflict.
        bcp_queue = queue<int>(); // BCP queue is cleared right on a conflict.
        if( is_fixed_lit(other_w_lit) ){  // or if( curr_decision_lvl == 0 ) ??
          conflict_on_fixed_variables = true;
        }else{
          learned_clause = clauses[cls];
        }
        return false;
      }else{
        if( !is_assigned_lit( other_w_lit ) ){  // Implication.
          assign( other_w_lit, curr_decision_lvl );
          bcp_queue.push( other_w_lit );

          if( curr_decision_lvl > 0 ){
            variables[abs(other_w_lit)].reason = cls;
          }
        } // Otherwise the other watched is assigned True: Clause satisfied.
        ++w;
      }
    }else{  // Found new watched literal.
      watchlist_add( clauses[cls][w_order], cls, w_order );
      w = w_list.erase(w);
    }
  }
  return true;
}


bool bcp()
{
  int bcp_source = 0;

  while( !bcp_queue.empty() ){
    bcp_source = bcp_queue.front();
    bcp_queue.pop();

    if( bcp_source > 0 ){
      if( !propagate( variables[bcp_source].negative_watchlist ) ){
        return false;
      }
    }else{
      if( !propagate( variables[-bcp_source].positive_watchlist ) ){
        return false;
      }
    }
  }

  return true;
}


//============================================================================//
//
//  1UIP
//
//============================================================================//


vector<int> resolve( const vector<int>& v1, const vector<int>& v2, int var )
{
  vector<int> is_taken( numof_variables + 1, 0 );
  vector<int> resolvent;

  for( auto t = v1.begin(); t != v1.end(); ++t ){
    if( abs(*t) != var && !is_fixed_lit(*t) ){
      if( is_taken[abs(*t)] == 0 ){
        is_taken[abs(*t)] = (*t > 0) ? 1 : -1;
        resolvent.push_back(*t);
      }else if( !same_sign(*t, is_taken[abs(*t)]) ){
        resolvent.clear();
        return resolvent;
      }
    }
  }

  for( auto t = v2.begin(); t != v2.end(); ++t ){
    if( abs(*t) != var && !is_fixed_lit(*t) ){
      if( is_taken[abs(*t)] == 0 ){
        is_taken[abs(*t)] = (*t > 0) ? 1 : -1;
        resolvent.push_back(*t);
      }else if( !same_sign(*t, is_taken[abs(*t)]) ){
        resolvent.clear();
        return resolvent;
      }
    }
  }

  return resolvent;
}


bool deletable( int lit, const set<int>& lits_in_clause )
{
  if( is_decided_var(abs(lit)) ){
    return false;
  }

  if( is_fixed_lit(lit) ){
    return true;
  }

  int r = variables[abs(lit)].reason;  // assert(r != 0);
  vector<int> reason_clause = clauses[r].literals;

  for( auto t = reason_clause.begin(); t != reason_clause.end(); ++t ){
    if( !same_var(lit, *t) ){
      if(
        lits_in_clause.find(*t) == lits_in_clause.end()
        && !deletable(*t, lits_in_clause)
      ){
        return false;
      }
    }
  }

  return true;
}


void minimize_learned_clause()
{
  set<int> lits_in_clause;
  for( int i = 0; i < learned_clause.size(); ++i ){
    lits_in_clause.insert( learned_clause[i] );
  }

  for(
    auto t = learned_clause.literals.begin();
    t != learned_clause.literals.end();
  ){
    if( deletable(*t, lits_in_clause) ){
      t = learned_clause.literals.erase(t);
    }else{
      ++t;
    }
  }
}


int lbd( vector<int>& lits )
{
  set<int> d_lvl_set;
  for( auto t = lits.begin(); t != lits.end(); ++t ){
    d_lvl_set.insert( variables[abs(*t)].decision_lvl );
  }
  return d_lvl_set.size();
}


void fuip_learned_clause()
{
  int var = 0;
  int cls = 0;
  int numof_curr_lvl_lits = 0;
  set<int> contributor_set;  // Variables involved in learning process.

  for( int i = 0; i < learned_clause.size(); ++i ){
    contributor_set.insert( abs(learned_clause[i]) );
    if( variables[abs(learned_clause[i])].decision_lvl == curr_decision_lvl ){
      ++numof_curr_lvl_lits;
      learned_clause.implication = learned_clause[i];
    }
  }

  while( numof_curr_lvl_lits > 1 ){
    // bool b = assign_stack.empty();assert(b == false);
    // Assignment stack should never be empty at this point.
    var = assign_stack.top();
    assign_stack.pop();

    for( int i = 0; i < learned_clause.size(); ++i ){
      if( abs(learned_clause[i]) == var ){
        cls = variables[var].reason;
        // if( clauses[cls].is_learned == true ){
        //   bump_clause_vsids( cls );
        // }
        learned_clause.literals = resolve(
          learned_clause.literals,
          clauses[cls].literals,
          var
        );
        // int sz = learned_clause.size(); assert(sz>0);
      }
    }

    deassign(var);
    numof_curr_lvl_lits = 0;
    for( int i = 0; i < learned_clause.size(); ++i ){
      contributor_set.insert( abs(learned_clause[i]) );
      if( variables[abs(learned_clause[i])].decision_lvl == curr_decision_lvl ){
        ++numof_curr_lvl_lits;
        learned_clause.implication = learned_clause[i];
      }
    }
  }

  minimize_learned_clause();

  learned_clause.lbd = lbd( learned_clause.literals );

  ++numof_conflicts;
  learned_lbd_sum += learned_clause.lbd;
  learned_lbd_queue.push( learned_clause.lbd );

  for( auto v = contributor_set.begin(); v != contributor_set.end(); ++v ){
    bump_variable_vsids( *v );
  }
}


//============================================================================//
//
//  conflict analysis
//
//============================================================================//


void add_learned_clause()
{
  // learned_clause.is_learned = true;
  clauses.push_back(learned_clause);
  ++numof_learned_clauses;

  watchlist_add( learned_clause[0], clauses.size() - 1, 0 );
  watchlist_add( learned_clause[1], clauses.size() - 1, 1 );

  // bump_clause_vsids( clauses.size() - 1 );
}


// deassign variables in assignment stack
void backtrack(int target_d_lvl)
{
  int var = 0;
  while( !assign_stack.empty() ){
    var = assign_stack.top();
    if( variables[var].decision_lvl > target_d_lvl ){
      assign_stack.pop();
      deassign(var);
    }else{
      break;
    }
  }

  curr_decision_lvl = target_d_lvl;

  if( !assign( learned_clause.implication, target_d_lvl ) ){  // Need assign!!!
    // Not sure if this block is needed. Probabaly not.
    conflict_on_fixed_variables = true;
    cerr<<"learned implication is reassigning a fixed variable!"<<endl;
  }
  if( target_d_lvl > 0 ){
    variables[abs(learned_clause.implication)].reason = clauses.size() - 1;
  }
    // implication must be assigned and set-attributes AFTER backtracking.

  bcp_queue.push( learned_clause.implication );
}


// add learned clause or not
// which level to backtrack to
int conflict_analysis()
{
  fuip_learned_clause();

  if( learned_clause.size() == 1 ){
    // Single-literal clause's implication must be correct to be SAT.
    // Hence single-literal clause is NOT added.
    return 0;
  }else{
    add_learned_clause();

    int backtrack_lvl = 0;
    int lit_decision_lvl = 0;
    for( int i = 0; i < learned_clause.size(); ++i ){
      lit_decision_lvl = variables[abs(learned_clause[i])].decision_lvl;
      if(
        lit_decision_lvl > backtrack_lvl
        && lit_decision_lvl < curr_decision_lvl
      ){
        backtrack_lvl = lit_decision_lvl;
      }
    }
    return backtrack_lvl;
  }
}



//============================================================================//
//
//  Checks if all variables are assigned in a lazy way.
//
//============================================================================//


bool all_assigned()
{
  if( !is_assigned_var(sat_sentinel) ){
    return false;
  }

  int initial_sat_sentinel = sat_sentinel;

  ++sat_sentinel;
  if( sat_sentinel == variables.size() ){
    sat_sentinel = 1;
  }

  while( is_assigned_var(sat_sentinel) && sat_sentinel != initial_sat_sentinel ){
    ++sat_sentinel;
    if( sat_sentinel == variables.size() ){
      sat_sentinel = 1;
    }
  }

  if(sat_sentinel == initial_sat_sentinel ){
    return true;
  }

  return false;
}



//============================================================================//
//
//  Make a new decision of assignment.
//
//============================================================================//

void decide()
{
  double max_vsids_score = 0.0;
  int decision = 0;

  for( int i = 1; i < variables.size(); ++i ){
    if ( !is_assigned_var(i) && variables[i].vsids_score > max_vsids_score ){
      max_vsids_score = variables[i].vsids_score;
      decision = i;
    }
  }

  if( variables[decision].last_assignment != 0 ){
    decision *= variables[decision].last_assignment;
  }else{
    decision = ( rand() % 2 ) ? decision : -decision;
  }

  assign( decision, curr_decision_lvl );
  bcp_queue.push( decision );
    // bcp_queue should've been empty before a decision: see bcp()
}



//============================================================================//
//
//  Restart backtracking. (No BCP queue push follows after backtrack.)
//
//============================================================================//

void restart_backtrack()
{
  int var = 0;
  while( !assign_stack.empty() ){
    var = assign_stack.top();
    assign_stack.pop();
    deassign(var);
  }
}



//============================================================================//
//
//  Search the problem for a SAT solution model, or determine UNSAT.
//  Return value:  0: unresolved, -1: UNSAT, 1: SAT.
//
//============================================================================//

int search()
{
  int backtrack_lvl = 0;

  while( true ){
    if( !bcp() ){  // Conflict.
      if( conflict_on_fixed_variables == true ){
        return -1;
      }else{
        assign_stack_size_queue.push( assign_stack.size() );
        if(
          learned_lbd_queue.is_full()
          && assign_stack_size_queue.is_full()
          && assign_stack.size() > R * assign_stack_size_queue.average()
        ){//cerr<<"p";
          learned_lbd_queue.clear();
        }
        decay_variable_vsids();
        // decay_clause_vsids();
        backtrack_lvl = conflict_analysis();
        backtrack( backtrack_lvl );
      }
    }else{  // Propagation finished peacefully.
      if( all_assigned() ){
        return 1;
      }else{
        if(
          learned_lbd_queue.is_full()
          && (learned_lbd_queue.average() * K
              > static_cast<double>(learned_lbd_sum) / numof_conflicts )
        ){//cerr<<"r";
          learned_clause.clear();
          learned_lbd_queue.clear();
          restart_backtrack();
          curr_decision_lvl = 0;
          return 0;  // Restart.
        }
        ++curr_decision_lvl;
        decide();
      }
    }
  }
}



//============================================================================//
//
//  Setting up a (re)start.
//  Return value:  0: unresolved, -1: UNSAT, 1: SAT.
//
//============================================================================//

bool solve()
{
  curr_decision_lvl = 0;

  int status = 0;

  while( status == 0 ){  // Each call of search is a (re)start.
    ++numof_restarts;
    total_numof_conflicts += numof_conflicts;
    numof_conflicts = 0;
    learned_lbd_sum = 0;
    status = search();
  }

  if( status == 1 ){
    return true;
  }else{
    return false;
  }
}



//============================================================================//
//
//  File output functions
//
//============================================================================//


void output_unsat(ofstream& ofs)
{
  ofs<<"s UNSATISFIABLE"<<endl;
}


void output_sat(ofstream& ofs)
{
  ofs<<"s SATISFIABLE"<<endl;
  ofs<<"v ";
  for( int i = 1; i <= numof_variables; ++i ){
    if(variables[i].value > 0){
      ofs<<i<<" ";
    }else if(variables[i].value < 0){
      ofs<<"-"<<i<<" ";
    }else{
      cerr<<"There is still unassigned variable"<<endl;
      exit(1);
    }
  }
  ofs<<"0"<<endl;
}



//============================================================================//
//
//  Main function
//
//============================================================================//

int main(int argc, char * argv[])
{
  srand(time(NULL));

  // string s = "aim-200-1_6-yes1-3.cnf";
  // parse_DIMACS_CNF(raw_clauses, numof_variables, s.c_str());
  parse_DIMACS_CNF(raw_clauses, numof_variables, argv[1]);

  //string file_name = s;
  string file_name = argv[1];
  string::iterator it = file_name.begin();
  for( ; it != file_name.end(); ++it){
    if(*it == '.'){
      break;
    }
  }
  file_name.replace(it, file_name.end(), ".sat");
    // For input file name 'ooo' or 'ooo.xxx', output file name is 'ooo.sat'.
  
  ofstream ofs(file_name.c_str(), ios_base::out|ios_base::trunc);
  if(!ofs.good()){
    cerr<<"Failed opening output file"<<endl;
    exit(1);
  }

  chrono::high_resolution_clock::time_point startTime
    = chrono::high_resolution_clock::now();

  initialize_variables();

  // Preprocessing ( Most basic )

  for( auto c = raw_clauses.begin(); c != raw_clauses.end(); ++c ){
    remove_duplicate_lit(*c);
  }

  if( !deal_with_1lit_clauses() ){
    cerr<<"Trivially UNSAT."<<endl;
    output_unsat(ofs);
    return 0;
  }

  initial_numof_clauses = raw_clauses.size();

  initialize_clauses();

  bool result = solve();

  chrono::high_resolution_clock::time_point finishTime
    = chrono::high_resolution_clock::now();
  auto duration
    = chrono::duration_cast<chrono::milliseconds>(finishTime-startTime).count();

  if(result){
    cout<<"SAT."<<endl;
    cout << endl << "time: " << duration << " ms" <<endl;
    output_sat(ofs);
  }else{
    cout<<"UNSAT."<<endl;
    cout << endl << "time: " << duration << " ms" <<endl;
    output_unsat(ofs);
  }

  ofs.close();

  return 0;
}
