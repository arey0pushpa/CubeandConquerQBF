/*-------------------------------------------------------------------------------------
 * Copyright (C) 2020
 * Johannes Kepler University Linz, Austria
 * Institute for Formal Models and Verification
 * Ankit Shukla

 * This file is a part of free software; you can redistribute it and/or
 * modify it under the terms of the GNU  General Public License as published
 * by the Free Software Foundation and included in this library;
 * either version 3 of the License, or any later version.
 --------------------------------------------------------------------------------------*/

/* TODOS:
 *.
 */

#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <future>
#include <iostream>
#include <iterator>
#include <limits> // std::numeric_limits
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <stdlib.h>
#include <string>
#include <sys/stat.h>
#include <vector>

#include <cassert>

#define INT_MAX std::numeric_limits<int>::max()
#define USE_SAT_LEAVES
// #define USE_QBF_LEAVES

namespace {
// --- General input and output ---

const std::string version = "0.0.1";
const std::string date = "27.01.2020";
const std::string program = "decision_heuristics";
const std::string author = "\"Ankit Shukla\"";
const std::string url = "\"https://github.com/arey0pushpa/CubeandConquerQBF\"";

enum class Error {
  file_reading = 1,
  file_writing = 2,
  file_pline = 3,
  num_vars = 4,
  allocation = 5,
  literal_read = 6,
  variable_value = 7,
  number_clauses = 8,
  empty_clause = 9,
  pseudoempty_clause = 10,
  empty_line = 11,
  num_cls = 12,
  illegal_comment = 13,
  invalid_args_count = 14,
  unexpected_eof = 15,
  invalid_dimacs_header = 16,
  var_too_large = 17,
  space_after_var = 18,
  end_of_line_0 = 19,
  unexpected_char = 20,
  input_format_violation = 21,
  decision_error = 22,
  formula_is_sat = 23,
  kappa_size_err = 24,
  var_notin_clause = 25,
  file_not_exist = 26,
  quant_alt = 27,
  trivial_false = 28
};

/* Extracting the underlying code of enum-classes (scoped enums) */
template <typename EC> inline constexpr int code(const EC e) noexcept {
  return static_cast<int>(e);
}

// --- Data structures for literals and variables; clause and clause-sets ---

typedef bool Value; // assignment: 0 = FALSE, 1 = TRUE
typedef std::int64_t lit_t;
typedef std::uint_fast32_t var_t;
typedef std::vector<lit_t> cl_t;   // clause type
typedef std::vector<cl_t> cls_t;   // clause-sets type
typedef std::vector<var_t> clv_t;  // pos clause type
typedef std::vector<double> cld_t; // clause type

cl_t varSwitch;
cls_t satCls; // Assigd lit will imply cls sat

class Clause {
public:
  Clause() {
    active = 1;
    size = 0;
  }
  var_t active;
  var_t size; // actual size of 'literals'
  cl_t e_literals;
  cl_t a_literals;

  // Only need to have pointers on literals
  int head_ptr;
  int tail_ptr;

  // Backtrack : (2n, 2n+1) pair
  cl_t bt_lvl;
  cl_t restore_ht;
};

class Variable {
public:
  Variable() {
    active = true;
    pure = false;
    quantype = 'a';
  }
  char quantype;
  bool active;
  bool pure;
  void initialise_qtype(char c) { quantype = c; }

  // Devise the head and tail pointers locations of the current variable
  cl_t head_ptrs;
  cl_t tail_ptrs;

  // A variable becomes pure if the size of one of the below set = 0
  cl_t pos_occ_cls;
  cl_t neg_occ_cls;
};

// Data Struture for info about input variables
std::vector<Variable> qbf_variables;
// Data structure for info about each input clause
std::vector<Clause> qbf_clauses;

bool unsat_bit = false; // assignment: 0 = FALSE, 1 = TRUE
var_t no_of_vars = 0;
var_t no_of_clauses = 0;
cl_t e_vars;
cl_t a_vars;
cl_t assgn_vars;
var_t active_cls = 0;
var_t active_vars = 0;
clv_t unit_cls;
unsigned long long nano_time;
std::string fname;
bool prop_fml = false;

cl_t pos_var_score;
cl_t neg_var_score;
cl_t uni_pos_cnt;
cl_t uni_neg_cnt;

std::random_device rd;
std::mt19937 gen(rd());
std::uniform_real_distribution<> dis(0,
                                     2); // uniform distribution between 0 and 1

void version_information() noexcept {
  std::cout << program
            << ":\n"
               " author: "
            << author
            << "\n"
               " url:\n  "
            << url
            << "\n"
               " Version: "
            << version
            << "\n"
               " Last change date: "
            << date << "\n";
  std::exit(0);
}

void headerError() { std::exit(code(Error::invalid_dimacs_header)); }
bool space(int ch) {
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

void formula_is_sat() {
  std::cout << "c The input formula is SAT. Promise me to not use it again!\n";
  std::exit(code(Error::formula_is_sat));
}

/** Trim Operations */
// trim from left
inline std::string &ltrim(std::string &s, const char *t = " \t\n\r\f\v") {
  s.erase(0, s.find_first_not_of(t));
  return s;
}

// trim from right
inline std::string &rtrim(std::string &s, const char *t = " \t\n\r\f\v") {
  s.erase(s.find_last_not_of(t) + 1);
  return s;
}

// trim from left & right
inline std::string &trim(std::string &s, const char *t = " \t\n\r\f\v") {
  return ltrim(rtrim(s, t), t);
}

// Basic extract int with
inline void extract_int(Clause *cls, std::string line, var_t cls_id) {
  lit_t lit;
  cl_t e_lits;
  cl_t a_lits;
  std::stringstream ss;
  std::string temp;

  ss << line;
  while (!ss.eof()) {
    ss >> temp;
    if (std::stringstream(temp) >> lit) {
      if (lit == 0)
        break;
      if (lit > INT_MAX)
        std::exit(code(Error::variable_value));
      if (qbf_variables[std::abs(lit)].quantype == 'a') {
        a_lits.push_back(lit);
      } else {
        assert(lit != 0);
        if (lit > 0) {
          qbf_variables[std::abs(lit)].pos_occ_cls.push_back(cls_id);
        } else {
          qbf_variables[std::abs(lit)].neg_occ_cls.push_back(cls_id);
        }
        e_lits.push_back(lit);
      }
    }
  }
  // Implement at least one of them is existensial quantified
  // tauto check implementation

  cls->e_literals = e_lits;
  cls->a_literals = a_lits;
  cls->size = e_lits.size() + a_lits.size();
  cls->head_ptr = 0;
  cls->tail_ptr = e_lits.size();
  qbf_variables[std::abs(e_lits[0])].head_ptrs.push_back(cls_id);
  qbf_variables[std::abs(e_lits[e_lits.size() - 1])].tail_ptrs.push_back(
      cls_id);
}

// Basic util
inline cl_t extract_jint(std::string line) {
  cl_t vec_int;
  std::stringstream ss;
  ss << line;
  std::string temp;
  lit_t found;
  while (!ss.eof()) {
    ss >> temp;
    if (std::stringstream(temp) >> found) {
      if (found > INT_MAX)
        std::exit(code(Error::variable_value));
      vec_int.push_back(found);
    }
  }
  // assert vec.back() == 0
  vec_int.pop_back();
  return vec_int;
}

// --- Extract the filename for the filepath
std::string getFileName(std::string filePath, bool withExtension = false,
                        char seperator = '/') {
  // Get last dot position
  std::size_t dotPos = filePath.rfind('.');
  std::size_t sepPos = filePath.rfind(seperator);

  if (sepPos != std::string::npos) {
    return filePath.substr(
        sepPos + 1,
        filePath.size() -
            (withExtension || dotPos != std::string::npos ? 1 : dotPos));
  }
  return "";
}

lit_t compare(const void *a, const void *b) {
  int lit1 = *((int *)a);
  int lit2 = *((int *)b);
  return (abs(lit1) - abs(lit2));
}

void print_filename(std::string filename) {
  std::cout << "c input filename " << filename << "\n";
}

void ReadDimacs(const std::string filename) {
  fname = getFileName(filename);
  std::ifstream fin(filename);
  if (!fin.is_open()) {
    perror(("c Error while opening file " + filename).c_str());
    std::exit(code(Error::file_reading));
  }
  bool p_line = false;
  bool clause_seen = false; // Used for e a definition after clause
  int matrix_cls_cnt = 0;

  char q_line = 'q';
  int q_alt = 0; // Using 1 based q_alt
  std::string line;

  while (std::getline(fin, line)) {
    if (line == "") {
      std::cout << "c Ignoring empty lines in the input file.\n";
      continue;
    }
    trim(line);
    char s1 = line[0];
    switch (s1) {
    case 'c': {
      break;
    }
    case 'p': {
      std::string s2;
      char ef = '\0';
      unsigned v, c;
      p_line = true;
      std::stringstream iss(line);
      iss >> s2 >> s2 >> v >> c >> ef;
      no_of_vars = v;
      no_of_clauses = c;
      if (s2 != "cnf" || ef != '\0') {
        std::cout << "c The input filename is: " << filename << "\n";
        std::cerr << "c Input format violation [p-line]. \nc Accepted "
                     "format: p cnf n1 n2"
                  << '\n';
        std::exit(code(Error::input_format_violation));
      }

      // Resize the variable object to total number of var + 1
      qbf_variables.resize(no_of_vars + 1);

      active_cls = no_of_clauses;
      active_vars = no_of_vars;

      // Use Nat_1 based indexing
      qbf_variables.resize(no_of_vars + 1);

      std::cout << "c\nc Found 'p cnf " << no_of_vars << ' ' << no_of_clauses
                << "' header. \n";
      break;
    }

    case 'e': {
      if (q_line == 'a' || q_line == 'q') {
        ++q_alt;
      }
      if (q_alt > 2) {
        std::cerr << "Number of Quantifier Alternations > 1. Input is not a "
                     "2QBF.\n";
        std::exit(code(Error::quant_alt));
      }
      if (clause_seen > 0) {
        print_filename(filename);
        std::cerr
            << "c Input format violation [e-line]. \nc e-line not allowed "
               "after matrix starts. "
            << '\n';
        std::exit(code(Error::input_format_violation));
      } else {
        q_line = 'e';
      }
      cl_t dummy_cls = extract_jint(line);
      assert(dummy_cls.size() >= 1);
      for (lit_t l : dummy_cls) {
        if (l < 1) {
          std::cerr << "c Input format violation. \nc Zero or Negative "
                       "variable in prefix."
                    << '\n';
          std::exit(code(Error::input_format_violation));
        }
        if (unsigned(abs(l)) > no_of_vars) {
          print_filename(filename);
          std::cerr << "c Input format violation. \nc atom > no_of_var."
                    << '\n';
          std::exit(code(Error::input_format_violation));
        }
        if (std::find(e_vars.begin(), e_vars.end(), l) != e_vars.end()) {
          std::cerr
              << "c Input format violation. \nc Repeated evars in the prefix."
              << '\n';
          std::exit(code(Error::input_format_violation));
        }
        e_vars.push_back(l);
      }
      break;
    }

    case 'a': {
      if (q_line == 'q' || q_line == 'e') {
        ++q_alt;
      }
      if (clause_seen > 0) {
        print_filename(filename);
        std::cerr
            << "c Input format violation [e-line]. \nc e-line not allowed "
               "after matrix starts. "
            << '\n';
        std::exit(code(Error::input_format_violation));
      } else {
        q_line = 'a';
      }
      cl_t dummy_cls = extract_jint(line);
      assert(dummy_cls.size() >= 1);
      for (lit_t l : dummy_cls) {
        if (l < 1) {
          std::cerr << "c Input format violation. \nc Zero or Negative "
                       "variable in prefix."
                    << '\n';
          std::exit(code(Error::input_format_violation));
        }
        if (unsigned(abs(l)) > no_of_vars) {
          print_filename(filename);
          std::cerr << "c Input format violation. \nc atom > no_of_var."
                    << '\n';
          std::exit(code(Error::input_format_violation));
        }
        if (std::find(a_vars.begin(), a_vars.end(), l) != a_vars.end()) {
          std::cerr
              << "c Input format violation. \n Repreated evars in the prefix."
              << '\n';
          std::exit(code(Error::input_format_violation));
        }
        a_vars.push_back(l);
      }
      break;
    }

    default: {
      if (p_line == false) {
        std::cout << "c p line absent in the input.\n";
        std::exit(code(Error::file_pline));
      }

      // Total four possible cases of the quant prefix
      if (clause_seen == false) {
        if (q_alt == 1 && q_line == 'a') { // All Universal case
          std::cout << "c Input formula is trivially false.\n";
          std::exit(code(Error::trivial_false));
        } else if (q_alt == 1 && q_line == 'e') { // SAT case
          std::cout << "c Input formula is a propositional formula.\n";
          prop_fml = true;
          // Exit the call. after this/r
        } else if (q_alt == 2 && q_line == 'a') { // EA case
          std::cout << "c Input formula is a ExistForall formula.\n";
        } else if (q_alt == 2 && q_line == 'e') { // AE case
          std::cout << "c Input formula is a ForallExists formula.\n";
        }
      }

      clause_seen = true;

      if (clause_seen == true) {
        // It's a 2QBF Forall Exists case or the SAT case :)
        assert(q_alt <= 2);
        assert(e_vars.size() + a_vars.size() <= no_of_vars);
        for (lit_t e : e_vars) {
          qbf_variables[e].initialise_qtype('e');
        }
      }

      // Push the clause in the qbf_clauses
      Clause *cls = new Clause;
      cls->active = 1;
      extract_int(cls, line, matrix_cls_cnt);
      qbf_clauses.push_back(*cls);
      if (qbf_clauses[matrix_cls_cnt].e_literals.size() == 0) {
        std::cout << "Clause with all universal literals. Trivially false.\n";
        std::exit(code(Error::trivial_false));
      }
      if (qbf_clauses[matrix_cls_cnt].e_literals.size() == 1)
        unit_cls.push_back(matrix_cls_cnt);
      ++matrix_cls_cnt;
      break;
    }
    }
  }
  if (no_of_clauses != matrix_cls_cnt) {
    print_filename(filename);
    std::cerr << "c Input format violation. \nc clause count == #matrix lines"
              << '\n';
    std::exit(code(Error::input_format_violation));
  } else if (!p_line) {
    print_filename(filename);
    std::cerr << "c Input format violation. \nc No p-line found!" << '\n';
    std::exit(code(Error::input_format_violation));
  }

  // initialize it with number of existential variables
  // TODO: Check off by one error
  pos_var_score.resize(e_vars.size() + 1);
  neg_var_score.resize(e_vars.size() + 1);
  uni_neg_cnt.resize(a_vars.size() + 1);
  uni_pos_cnt.resize(a_vars.size() + 1);
}

/* / Apply assignment application to the formula
cld_t ApplyAssmnt(cld_t &Fml, const cls_t &ass) {
  var_t sz = ass.size();
  assert(sz >= 1);
  for (var_t i = sz; i > 0; --i) {
  }
} */

// -- Update Data Structure based on the chosen decision variable ---
std::string DataStructureUpdate(lit_t dvar) {
  cl_t sat_cls_set, unsat_cls_set;
  if (dvar == 0)
    std::exit(code(Error::variable_value));
  // Unlear why this check is required
  if (qbf_variables[std::abs(dvar)].active == false) {
    return "NONE";
  }
  // Remove the assigned variable from active vars
  qbf_variables[std::abs(dvar)].active = false;
  assert(active_vars > 0);
  --active_vars;
  // Clauses where the variable occurs positive and negative
  if (dvar > 0) {
    sat_cls_set = qbf_variables[std::abs(dvar)].pos_occ_cls;
    unsat_cls_set = qbf_variables[std::abs(dvar)].neg_occ_cls;
  } else {
    sat_cls_set = qbf_variables[std::abs(dvar)].neg_occ_cls;
    unsat_cls_set = qbf_variables[std::abs(dvar)].pos_occ_cls;
  }
  for (var_t c : sat_cls_set) {
    if (qbf_clauses[c].active == 0) {
      continue;
    }
    // If the decision var satisfies an active clause
    if (qbf_clauses[c].active == 1) {
      assert(active_cls > 0);
      --active_cls;
    }
    qbf_clauses[c].active = 0;
  }
  // Implemet early exit based on number of clauses/ i.e active_cls == 0
  if (active_cls == 0) {
    // We do not handle SAT formula checking for heuristic 4 and 5
    unsat_bit = true;
    return "UNSAT";
  }

  dvar *= -1;
  for (var_t c : unsat_cls_set) {
    if (qbf_clauses[c].active == 0) {
      continue;
    }
    var_t hdptr = qbf_clauses[c].head_ptr;
    var_t tlptr = qbf_clauses[c].tail_ptr;

    // Single var UNSAT case
    if (hdptr == tlptr) {
      assert(qbf_clauses[c].e_literals[hdptr] == dvar);
      assert(qbf_clauses[c].e_literals[tlptr] == dvar);
      unsat_bit = true;
      return "UNSAT";
    }
    assert(hdptr < tlptr);
    // Two or more variable case
    if (qbf_clauses[c].e_literals[hdptr] == dvar) {
      while (
          qbf_variables[std::abs(
                            qbf_clauses[c].e_literals[qbf_clauses[c].head_ptr])]
              .active == false) {
        ++qbf_clauses[c].head_ptr;
      }

    } else if (qbf_clauses[c].e_literals[tlptr] == dvar) {
      while (
          qbf_variables[std::abs(
                            qbf_clauses[c].e_literals[qbf_clauses[c].tail_ptr])]
              .active == false) {
        --qbf_clauses[c].tail_ptr;
      }
    }
    assert(qbf_clauses[c].head_ptr <= qbf_clauses[c].tail_ptr);
    --qbf_clauses[c].size;
    if (qbf_clauses[c].head_ptr == qbf_clauses[c].tail_ptr) {
      unit_cls.push_back(c);
    }
  }
  if (active_cls == 0)
    formula_is_sat();
  return "NONE";
}

// -- UCP : Unit Constraint Propagation ----
void UnitPropagation(var_t c) {
  var_t hdctr;
  assert(unit_cls.size() > 0);
  unit_cls.pop_back();
  hdctr = qbf_clauses[c].head_ptr;
  assert(hdctr == qbf_clauses[c].tail_ptr);
  if (DataStructureUpdate(qbf_clauses[c].e_literals[hdctr]) == "UNSAT") {
    unsat_bit = true;
    unit_cls.clear();
  }
}

std::string UnitConstraintPropogation(cls_t &Impl_ass, cl_t &Impl_lvl,
                                      cl_t &satcls_tmp, cl_t &Assgn_lits) {
  bool ut = 0;
  if (unit_cls.size() > 0)
    ut = 1;
  cl_t impl_vars;
  while (unit_cls.size() > 0) {
    var_t cls = unit_cls[unit_cls.size() - 1];
    var_t hdctr = qbf_clauses[cls].head_ptr;
    // TODO: Implement the unit literal check for univ var
    // assert(qbf_clauses[cls].e_literals[hdctr] > 1);
    lit_t unitv = qbf_clauses[cls].e_literals[hdctr];
    impl_vars.push_back(unitv);
    lit_t assv = Assgn_lits.back();
    int sz = Assgn_lits.size();
    if (assv > 0 && sz != 0) {
      if (std::find(qbf_variables[assv].neg_occ_cls.begin(),
                    qbf_variables[assv].neg_occ_cls.end(),
                    cls) == qbf_variables[assv].neg_occ_cls.end())
        satcls_tmp.push_back(cls);

    } else if (assv < 0 && sz != 0) {
      if (std::find(qbf_variables[assv].neg_occ_cls.begin(),
                    qbf_variables[assv].neg_occ_cls.end(),
                    cls) == qbf_variables[assv].neg_occ_cls.end())
        satcls_tmp.push_back(cls);
    }

    UnitPropagation(cls);
  }
  Impl_ass.push_back(impl_vars);
  Impl_lvl.push_back(Assgn_lits.size());
  if (unsat_bit == true)
    return "UNSAT";
  // UpdateVarStat(heuristic);
  return "NONE";
}

cls_t UnionAss(const cls_t &dec, const cls_t &impl) {
  cls_t ass;
  ass.reserve(dec.size() + impl.size()); // preallocate memory
  ass.insert(ass.end(), dec.begin(), dec.end());
  ass.insert(ass.end(), impl.begin(), impl.end());
  return ass;
}

// Implement negation of the cls
cl_t NegCls(cl_t &cls) {
  cl_t neg_cls;
  for (lit_t l : cls) {
    neg_cls.push_back(-l);
  }
  return neg_cls;
}

var_t CountPurevar() {
  var_t pureCount = 0;
  for (var_t i = 0; i < a_vars.size(); ++i) {
    if (pos_var_score[i] == 0 || neg_var_score[i] == 0)
      ++pureCount;
  }
  return pureCount;
}

/*** Two-Sided Jeroslow Wang Heuristic ***/
void DecHeuristic(lit_t l) {
  if (l > 0) {
    pos_var_score[std::abs(l)] += 1;
  } else {
    neg_var_score[std::abs(l)] += 1;
  }
}

// Compute the Heuristical Score of each variable
var_t HeuristicScore() {
  std::fill(pos_var_score.begin(), pos_var_score.end(), 0);
  std::fill(neg_var_score.begin(), neg_var_score.end(), 0);

  var_t total_active_cls = 0;

  for (var_t i = 0; i < qbf_clauses.size(); ++i) {
    if (qbf_clauses[i].active != 1) {
      continue;
    } else {
      ++total_active_cls;
      var_t size = qbf_clauses[i].size;
      var_t elem_cnt = 0;
      for (var_t j = 0; j <= qbf_clauses[i].a_literals.size(); ++j) {
        lit_t l = qbf_clauses[i].a_literals[j];
        if (qbf_variables[std::abs(l)].active == false)
          continue;
        ++elem_cnt;
        DecHeuristic(l);
      }
    }
    //  assert(elem_cnt == size);
  }

  if (total_active_cls == 0) {
    formula_is_sat();
  }
}

var_t VariableSelection() {
  var_t top_var = 0;
  var_t top_var_cnt =
      0; // be careful be update it when change the heuristic val
  var_t max_pol;
  assert(pos_var_score.size() == neg_var_score.size());
  for (var_t var = 1; var < pos_var_score.size(); ++var) {
    if (qbf_variables[var].active == false)
      continue;
    max_pol = pos_var_score[var] * neg_var_score[var];
    if (max_pol < top_var_cnt) {
      continue;
    } else {
      top_var_cnt = max_pol;
      top_var = var;
    }
  }
  return top_var;
}

// Look Ahead Heuristic
lit_t LookAhead() {
  var_t the_chosen_one;
  var_t max_score = 0;

  var_t max_pol;
  assert(pos_var_score.size() == neg_var_score.size());

  HeuristicScore();

  the_chosen_one = VariableSelection();

  return the_chosen_one;
}

// BackTrack function that restore the header and the univ var
void BackTrack(const int bl) {
  for (int i = 0; i < qbf_clauses.size(); ++i) {
    if (qbf_clauses[i].active == false)
      continue;
    // Remove the backtrack storage till the relevant level
    while (qbf_clauses[i].bt_lvl.back() > bl) {
      qbf_clauses[i].bt_lvl.pop_back();
      qbf_clauses[i].restore_ht.pop_back();
      qbf_clauses[i].restore_ht.pop_back();
    }
    // Assign the head and tail to the current bactrack lvl
    int sz = qbf_clauses[i].restore_ht.size();
    qbf_clauses[i].head_ptr = qbf_clauses[i].restore_ht[sz - 1];
    qbf_clauses[i].tail_ptr = qbf_clauses[i].restore_ht[sz - 2];
  }
}

// ---- Generate Subformulas -------------
#ifdef USE_SAT_LEAVES
void GenerateSubFml(cls_t &LCubes, cls_t &LClause, cl_t &Assgn_lits,
                    cls_t &Impl_ass, cl_t Impl_lvl) {
  cl_t satcls_tmp;
  // Step 1: Uni Prop
  std::string up =
      UnitConstraintPropogation(Impl_ass, Impl_lvl, satcls_tmp, Assgn_lits);
  // Step 2: If the unit propogation returns UNSAT exit
  if (up == "UNSAT") {
    return;
  }
  // Step 3. Perform Lookahead
  lit_t l = LookAhead(); // Top node of the Search Tree
  Assgn_lits.push_back(l);
  // Store the head and ptr for the backtrack
  if (l > 0) {
    for (lit_t c1 : qbf_variables[std::abs(l)].neg_occ_cls) {
      assert(c1 > 0);
      int hd = qbf_clauses[c1].head_ptr;
      int tl = qbf_clauses[c1].tail_ptr;
      qbf_clauses[c1].bt_lvl.push_back(Assgn_lits.size());
      qbf_clauses[c1].restore_ht.push_back(hd);
      qbf_clauses[c1].restore_ht.push_back(tl);
    }

    satcls_tmp = qbf_variables[std::abs(l)].pos_occ_cls;
  } else {
    for (lit_t c1 : qbf_variables[std::abs(l)].pos_occ_cls) {
      assert(c1 > 0);
      int hd = qbf_clauses[c1].head_ptr;
      int tl = qbf_clauses[c1].tail_ptr;
      qbf_clauses[c1].bt_lvl.push_back(Assgn_lits.size());
      qbf_clauses[c1].restore_ht.push_back(hd);
      qbf_clauses[c1].restore_ht.push_back(tl);
    }

    satcls_tmp = qbf_variables[std::abs(l)].neg_occ_cls;
  }

  int psize = qbf_variables[std::abs(l)].pos_occ_cls.size();
  varSwitch.push_back(0);
  bool root_flipped = false;

  // Step 4: Iteration call of the loop. Untill all the combinations are tried
  while (Assgn_lits.size() == 0) { // Remaining tree
    // Step 1: Uni Prop
    UnitConstraintPropogation(Impl_ass, Impl_lvl, satcls_tmp, Assgn_lits);
    // Push the Clausebsatisfied by the decision and implied assgn
    satCls.push_back(satcls_tmp);
    satcls_tmp.clear();

    // Step 2: Cuttoff Criteria 1: Cuttoff Heuristic
    if (Assgn_lits.size() == 10 || DataStructureUpdate(l) == "UNSAT") {
      lit_t rvar = Assgn_lits.back();
      Assgn_lits.erase(Assgn_lits.end() - 1);
      while (varSwitch.back() == 1) { // Tried both polarity
        varSwitch.erase(varSwitch.end() - 1);
        rvar = Assgn_lits.back();
        Assgn_lits.erase(Assgn_lits.end() - 1);
      }
      if (Assgn_lits.size() == 0)
        break;
      cl_t satcls_list;
      // Restore activity of the unit clauses
      // TODO: Check off by one error
      while (satCls.size() > Assgn_lits.size()) {
        for (lit_t l1 : satCls.back()) {
          satcls_list.push_back(l1);
          satCls.pop_back();
        }
      }
      for (lit_t l2 : satcls_list) {
        qbf_clauses[l2].active = true;
      }

      // Backtrack to the previous decisioon level
      BackTrack(Assgn_lits.size());
      varSwitch.push_back(1);
      Assgn_lits.push_back(-rvar);
    }

    // Step 3. Perform Lookahead
    l = LookAhead();
    Assgn_lits.push_back(l);
  }
  return;
}

#endif //

// --- Parse Commandline argument ---
void show_usage() noexcept {
  std::cout << "2QBFCC.cpp [version 0.1]. (C) Copyright 2020 "
               "\nUsage: ./2QBFCC [filename]\n";
  std::exit(0);
}

// --- Printing basic information about the tool ---
static void banner() {
  std::cout << "c 2QBF Cube and Conquer based Heuristic.\n"
               "c Version: "
            << version
            << "\nc Copyright (c) 2020 Johannes Kepler University.\n";
}

// --- Print Output --- //
void output(const std::string filename) {
  std::cout << "c\nc Program information:\n";
  std::cout << "c " << fname << " " << assgn_vars.size() << "\n";
  std::exit(0);
}

// --- File existence check ----//
bool fileExists(const std::string &name) {
  struct stat buffer;
  return (stat(name.c_str(), &buffer) == 0);
}

} // namespace

int main(const int argc, const char *const argv[]) {
  // ---------- [Command Line Arguments Parsing Starts] ------------
  if (argc == 1 || argc > 2) {
    std::cout << "Invalid number of arguments.\n";
    std::exit(code(Error::invalid_args_count));
  }

  const std::string filename = argv[1];

  if (filename == "-v" or filename == "--version")
    version_information();
  if (filename == "-h" or filename == "--help")
    show_usage();
  // [Command Line Arguments Parsing Ends]

  banner();

  // -------- [Parsing Input Starts] ----------------
  ReadDimacs(filename);
  // [Parsing Input Ends]

  // ------- [2QBF-Heuristic Algorithm Starts] ------------
  cls_t LCubes, LClauses, Impl_ass;
  cl_t Assgn_lits, Impl_lvl;

  // ------- [Cube Phase Starts] --------------
  GenerateSubFml(LCubes, LClauses, Assgn_lits, Impl_ass, Impl_lvl);
  // ------- [Cube Phase Ends] --------------

  // ------- [Conquer Phase Starts] --------------
  /* Conquer();
  for (const cls_t &c : Cubes) {
    SAT(CreateFml(Fml, Cubes, Cls));
  }*/

  // ------- [Conquer Phase Ends] --------------

  // [2QBF-Heuristic Algorithm Ends]

  output(filename);

  return 0;
}
