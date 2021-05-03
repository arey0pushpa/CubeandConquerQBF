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
// #define USE_SAT_LEAVES
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

  // Restore Level based
  int rst_lvl;
};

class Variable {
public:
  Variable() {
    active = 2;
    pure = false;
    quantype = 'a';
    ass_level = 0;
  }
  char quantype;
  var_t active; // 0: Assgn false, 1: Assigned true, 2 : Unassigned
  bool pure;
  var_t ass_level;
  void initialise_qtype(char c) { quantype = c; }

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
int no_of_leaves = 0;

cl_t pos_var_score;
cl_t neg_var_score;
cl_t pure_lit_score;
cl_t avars_indx;

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
        e_lits.push_back(lit);
      }
      assert(lit != 0);
      if (lit > 0) {
        qbf_variables[std::abs(lit)].pos_occ_cls.push_back(cls_id);
      } else {
        qbf_variables[std::abs(lit)].neg_occ_cls.push_back(cls_id);
      }
    }
  }
  // Implement at least one of them is existensial quantified
  // tauto check implementation

  cls->e_literals = e_lits;
  cls->a_literals = a_lits;
  cls->size = e_lits.size() + a_lits.size();
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

// --- Print Output --- //
void output(const std::string filename) {
  std::cout << "c\nc Program information:\n";
  std::cout << "c " << fname << " " << no_of_leaves << "\n";
  std::exit(0);
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
  pos_var_score.resize(a_vars.size());
  neg_var_score.resize(a_vars.size());
  pure_lit_score.resize(a_vars.size());
  avars_indx.resize(no_of_vars);
  // Updated to assign only universal variables
  active_vars = a_vars.size();

  // Initialize the avars_indx
  // std::iota(avars_indx.begin(), avars_indx.end(), 0);
  int ida = 0;
  for (lit_t l : a_vars) {
    assert(l > 0);
    avars_indx[l] = ida;
    ++ida;
  }
}

/* / Apply assignment application to the formula
cld_t ApplyAssmnt(cld_t &Fml, const cls_t &ass) {
  var_t sz = ass.size();
  assert(sz >= 1);
  for (var_t i = sz; i > 0; --i) {
  }
} */

void IncrementVarScore(lit_t l) {
  if (l > 0) {
    // TODO: Require mapping the index and the value.
    pos_var_score[avars_indx[std::abs(l)]] += 1;
  } else {
    neg_var_score[avars_indx[std::abs(l)]] += 1;
    // neg_var_score[std::abs(l)] += 1;
  }
}

// Compute the Heuristical Score of each variable
var_t HeuristicScoreUpdate() {
  for (lit_t a : a_vars) {
    assert(a > 0);
    if (qbf_variables[a].active == 0 || qbf_variables[a].active == 1) {
      // TODO: Require mapping the index and the value.
      pos_var_score[avars_indx[a]] == 1;
      pos_var_score[avars_indx[a]] == 1;
    }
  }
}

// Compute the Heuristical Score of each variable
var_t HeuristicScore() {
  std::fill(pos_var_score.begin(), pos_var_score.end(), 0);
  std::fill(neg_var_score.begin(), neg_var_score.end(), 0);

  for (var_t i = 0; i < a_vars.size(); ++i) {
    std::fill(pure_lit_score.begin(), pure_lit_score.end(), 0);
    var_t indx = a_vars[i];
    cl_t sat_cls_set;
    if (qbf_variables[indx].active == 0 || qbf_variables[indx].active == 1)
      continue;
    // Clauses where the variable occurs positive and negative
    int pidx = 0;
    sat_cls_set = qbf_variables[indx].pos_occ_cls;
    for (int c = 0; c < qbf_clauses.size(); ++c) {
      if (qbf_clauses[c].active == 0)
        continue;
      if (c == sat_cls_set[pidx]) {
        ++pidx;
        continue;
      }
      for (lit_t l : qbf_clauses[c].a_literals) {
        if (qbf_variables[std::abs(l)].active == 0 ||
            qbf_variables[std::abs(l)].active == 1)
          continue;
        assert(0 <= pure_lit_score[avars_indx[std::abs(l)]] <= 3);
        if (pure_lit_score[avars_indx[std::abs(l)]] == 3)
          continue;
        if (l > 0) {
          // 1 : Negative, 2 : positive, 3: Not pure
          if (pure_lit_score[avars_indx[std::abs(l)]] == 0) {
            pure_lit_score[avars_indx[std::abs(l)]] = 2;
          } else if (pure_lit_score[avars_indx[std::abs(l)]] == 1) {
            pure_lit_score[avars_indx[std::abs(l)]] = 3;
          }
        } else {
          if (pure_lit_score[avars_indx[std::abs(l)]] == 0) {
            pure_lit_score[avars_indx[std::abs(l)]] = 1;
          } else if (pure_lit_score[avars_indx[std::abs(l)]] == 2) {
            pure_lit_score[avars_indx[std::abs(l)]] = 3;
          }
        }
      }
    }
    int pscore = 0;
    for (int m = 0; m < pure_lit_score.size(); ++m) {
      if (pure_lit_score[m] == 1 || pure_lit_score[m] == 2)
        ++pscore;
    }
    pos_var_score[avars_indx[a_vars[i]]] = pscore;
  }

  for (var_t i = 0; i < a_vars.size(); ++i) {
    std::fill(pure_lit_score.begin(), pure_lit_score.end(), 0);
    var_t indx = a_vars[i];
    cl_t sat_cls_set;
    if (qbf_variables[indx].active == 0 || qbf_variables[indx].active == 1)
      continue;
    // Clauses where the variable occurs positive and negative
    int nidx = 0;
    sat_cls_set = qbf_variables[indx].neg_occ_cls;
    for (int c = 0; c < qbf_clauses.size(); ++c) {
      if (qbf_clauses[c].active == 0)
        continue;
      if (c == sat_cls_set[nidx]) {
        ++nidx;
        continue;
      }
      for (lit_t l : qbf_clauses[c].a_literals) {
        if (qbf_variables[std::abs(l)].active == 0 ||
            qbf_variables[std::abs(l)].active == 1)
          continue;
        assert(0 <= pure_lit_score[avars_indx[std::abs(l)]] <= 3);
        if (pure_lit_score[avars_indx[std::abs(l)]] == 3)
          continue;
        if (l > 0) {
          // 1 : Negative, 2 : positive, 3: Not pure
          if (pure_lit_score[avars_indx[std::abs(l)]] == 0) {
            pure_lit_score[avars_indx[std::abs(l)]] = 2;
          } else if (pure_lit_score[avars_indx[std::abs(l)]] == 1) {
            pure_lit_score[avars_indx[std::abs(l)]] = 3;
          }
        } else {
          if (pure_lit_score[avars_indx[std::abs(l)]] == 0) {
            pure_lit_score[avars_indx[std::abs(l)]] = 1;
          } else if (pure_lit_score[avars_indx[std::abs(l)]] == 2) {
            pure_lit_score[avars_indx[std::abs(l)]] = 3;
          }
        }
      }
    }
    int nscore = 0;
    for (int m = 0; m < pure_lit_score.size(); ++m) {
      if (pure_lit_score[m] == 1 || pure_lit_score[m] == 2)
        ++nscore;
    }
    neg_var_score[avars_indx[a_vars[i]]] = nscore;
  }
}

// During elimination calulate the pre lits
var_t PureLitElimScore() {
  std::fill(pos_var_score.begin(), pos_var_score.end(), 0);
  std::fill(neg_var_score.begin(), neg_var_score.end(), 0);

  var_t total_active_cls = 0;

  for (var_t i = 0; i < qbf_clauses.size(); ++i) {
    if (qbf_clauses[i].active != 1) {
      continue;
    } else {
      ++total_active_cls;
      for (var_t j = 0; j < qbf_clauses[i].a_literals.size(); ++j) {
        lit_t l = qbf_clauses[i].a_literals[j];
        if (qbf_variables[std::abs(l)].active == 0 ||
            qbf_variables[std::abs(l)].active == 1)
          continue;
        IncrementVarScore(l);
      }
    }
  }

  if (total_active_cls == 0) {
    formula_is_sat();
  }
}

// Pure Literal Elimination
void PureLitElim(cls_t &Impl_ass, cl_t &Impl_lvl, cl_t &Assgn_lits) {
  cl_t impl_vars;
  var_t pureCount = 0;
  PureLitElimScore();
  for (var_t i = 0; i < a_vars.size(); ++i) {
    var_t indx = a_vars[i];
    if (qbf_variables[indx].active == 0 || qbf_variables[indx].active == 1)
      continue;
    if (pos_var_score[avars_indx[indx]] == 0 ||
        neg_var_score[avars_indx[indx]] == 0) {
      if (pos_var_score[avars_indx[indx]] == 0) {
        impl_vars.push_back(a_vars[i]);
        // Below is Incorrect> TODO avoid redoing this process in
        // DataStructureUpdate
        qbf_variables[indx].active = 1;
      } else {
        impl_vars.push_back(-a_vars[i]);
        qbf_variables[indx].active = 0;
      }
      ++pureCount;
      --active_vars; // Only Universal variable for now
    }
  }
  Impl_ass.push_back(impl_vars);
  Impl_lvl.push_back(Assgn_lits.size());

  return;
}

// -- Update Data Structure based on the chosen decision variable ---
std::string DataStructureUpdate(cls_t &Impl_ass, cl_t &Impl_lvl,
                                cl_t &Assgn_lits, lit_t dvar) {
  cl_t sat_cls_set, unsat_cls_set;
  if (dvar == 0)
    std::exit(code(Error::variable_value));

  // Remove the assigned variable from active vars
  if (dvar > 0) {
    qbf_variables[std::abs(dvar)].active = 1;
  } else {
    qbf_variables[std::abs(dvar)].active = 0;
  }
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
  if (active_cls == 0 || active_vars == 0) {
    // We do not handle SAT formula checking for heuristic 4 and 5
    unsat_bit = true;
    return "UNSAT";
  }

  PureLitElim(Impl_ass, Impl_lvl, Assgn_lits);
}

void Reduction(cls_t &Impl_ass, cl_t &Impl_lvl, cl_t &Assgn_lits) {
  PureLitElim(Impl_ass, Impl_lvl, Assgn_lits);
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

var_t VariableSelection() {
  lit_t top_var = -1;
  var_t top_var_cnt =
      0; // be careful be update it when change the heuristic val
  var_t max_pol;
  assert(pos_var_score.size() == neg_var_score.size());
  for (var_t i = 0; i < pos_var_score.size(); ++i) {
    if (qbf_variables[a_vars[i]].active == 0 ||
        qbf_variables[a_vars[i]].active == 1)
      continue;
    max_pol = pos_var_score[i] * neg_var_score[i];
    // Degen case handling to select first variable
    if (max_pol == top_var_cnt && top_var == -1) {
      top_var_cnt = max_pol;
      top_var = i;
    }
    if (max_pol < top_var_cnt) {
      continue;
    } else {
      top_var_cnt = max_pol;
      top_var = i;
    }
  }
  // If this is violated then the all vars are already assigned
  assert(top_var >= 0);
  return a_vars[top_var];
  // return a_vars[avars_indx[top_var]];
}

// Look Ahead Heuristic
lit_t LookAhead() {
  var_t the_chosen_one;
  var_t max_score = 0;

  var_t max_pol;
  assert(pos_var_score.size() == neg_var_score.size());

  HeuristicScore();

  the_chosen_one = VariableSelection();

  if (the_chosen_one == 0) {
    output(fname);
    std::exit(0);
  }

  return the_chosen_one;
}

// BackTrack function that restore the header and the univ var
void BackTrack(cls_t &Impl_ass, cl_t Impl_lvl, cl_t &Assgn_lits, int bl) {
  while (Assgn_lits.size() != bl) {
    cl_t sat_cls;
    lit_t dlit = Assgn_lits.back();
    Assgn_lits.erase(Assgn_lits.end() - 1);
    ++active_vars; // Increase the count to reflect the bt
    if (dlit > 0) {
      sat_cls = qbf_variables[std::abs(dlit)].pos_occ_cls;
    } else {
      sat_cls = qbf_variables[std::abs(dlit)].neg_occ_cls;
    }

    for (var_t c : sat_cls) {
      if (qbf_clauses[c].active == true)
        continue;
      if (qbf_clauses[c].rst_lvl == bl) {
        qbf_clauses[c].active = true;
        qbf_clauses[c].rst_lvl = 0;
      }
    }

    cl_t impl_ass = Impl_ass.back();
    lit_t impl_lvl = Impl_lvl.back();
    Impl_lvl.erase(Impl_lvl.end() - 1);
    Impl_ass.erase(Impl_ass.end() - 1);

    assert(impl_lvl == bl); // TODO: Check off by one error

    for (lit_t l : impl_ass) {
      qbf_variables[l].active = 2;
      ++active_vars; // Increase the count to reflect the bt
    }

    --bl;
  }
}

// ---- Generate Subformulas -------------
// #ifdef USE_SAT_LEAVES
int TreeSize(cls_t &Impl_ass, cl_t Impl_lvl, cl_t &Assgn_lits) {
  int tSize = 0;
  // Step 1: Pure Lit Elimination
  Reduction(Impl_ass, Impl_lvl, Assgn_lits);
  // PureLitElim(Impl_ass, Impl_lvl, Assgn_lits);

  // Step 2: If the unit propogation returns UNSAT exit
  if (active_cls == 0 || active_vars == 0) {
    std::cout << "\nc The Formula is Solvable without LookAhead.\n";
    return 0; // Input formula is false
  }

  // Step 3. Perform Lookahead
  lit_t l = LookAhead() * -1; // Top node of the Search Tree
  Assgn_lits.push_back(l);

  // int psize = qbf_variables[std::abs(l)].pos_occ_cls.size();
  varSwitch.push_back(0);
  bool root_flipped = false;

  // Step 4: Iteration call of the loop. Untill all the combinations are
  // tried
  while (Assgn_lits.size() != 0) { // Remaining tree
    // Step 1: Pure Lit Elim
    // PureLitElim(Impl_ass, Impl_lvl, Assgn_lits);

    // Step 2: Cuttoff Criteria 1: Cuttoff Heuristic
    std::string dupdate =
        DataStructureUpdate(Impl_ass, Impl_lvl, Assgn_lits, l);

    // What do mean if a branch is SAT?
    // Just count as a leaf node
    if (dupdate == "UNSAT" || dupdate == "SAT") {
      ++tSize;
      // lit_t rvar = Assgn_lits.back();
      int alit_size = Assgn_lits.size();
      assert(alit_size == varSwitch.size()); // Invariant
      // Assgn_lits.erase(Assgn_lits.end() - 1);
      while (varSwitch.back() == 1) { // Tried both polarity
        varSwitch.erase(varSwitch.end() - 1);
        --alit_size;
        // Assgn_lits.erase(Assgn_lits.end() - 1);
      }
      assert(alit_size == varSwitch.size());
      if (alit_size < 0) // If it's 0 check the off by one
        break;

      // Backtrack to the previous decisioon level
      BackTrack(Impl_ass, Impl_lvl, Assgn_lits, alit_size);

      // Switch the polarity of the variable: True branch taken
      assert(varSwitch.back() == 0);
      varSwitch.erase(varSwitch.end() - 1);
      varSwitch.push_back(1);

      // Revert back the polarity of the chosen variable
      l = Assgn_lits.back();
      Assgn_lits.erase(Assgn_lits.end() - 1);
      // Assgn_lits.push_back(-Assgn_lits[alit_size]);
      Assgn_lits.push_back(-l);
      l *= -1;
      continue;
    }

    // Step 3. Perform Lookahead
    l = LookAhead();
    Assgn_lits.push_back(l);
  }
  return tSize;
}
// #endif //

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

  // [Parsing Input Starts]
  ReadDimacs(filename);
  // [Parsing Input Ends]

  // [2QBF-Heuristic Algorithm Starts]
  cls_t Impl_ass;
  cl_t Assgn_lits, Impl_lvl;

  // [Cube Phase Starts]
  no_of_leaves = TreeSize(Impl_ass, Impl_lvl, Assgn_lits);
  // [Cube Phase Ends]

  // [2QBF-Heuristic Algorithm Ends]

  output(filename);

  return 0;
}
