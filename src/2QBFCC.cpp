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
 */

#include <stdlib.h>
#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <future>
#include <iostream>
#include <iterator>
#include <limits>  // std::numeric_limits
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include <cassert>

#define INT_MAX std::numeric_limits<int>::max()
namespace {
// --- General input and output ---

const std::string version = "0.0.1";
const std::string date = "27.01.2020";
const std::string program = "decision_heuristics";
const std::string author = "\"Ankit Shukla\"";
const std::string url = "\"https://github.com/arey0pushpa/watermellon\"";

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
  var_notin_clause = 25
};

/* Extracting the underlying code of enum-classes (scoped enums) */
template <typename EC>
inline constexpr int code(const EC e) noexcept {
  return static_cast<int>(e);
}

// --- Data structures for literals and variables; clause and clause-sets ---

typedef bool Value;  // assignment: 0 = FALSE, 1 = TRUE
typedef std::int64_t lit_t;
typedef std::uint_fast32_t var_t;
typedef std::vector<lit_t> cl_t;    // clause type
typedef std::vector<var_t> clv_t;   // clause type
typedef std::vector<double> cld_t;  // clause type

class Clause {
 public:
  Clause() {
    active = 1;
    size = 0;
    head_ctr = 0;
    tail_ctr = 0;
  }
  var_t active;
  var_t size;  // actual size of 'literals'
  cl_t literals;
  var_t head_ctr;
  var_t tail_ctr;
};

class Variable {
 public:
  Variable() {
    active = true;
  }
  bool active;
  cl_t pos_occ_cls;
  cl_t neg_occ_cls;
};

// Data Struture for info about input variables
std::vector<Variable> cnf_variables;
// Data structure for info about each input clause
std::vector<Clause> cnf_clauses;

var_t no_of_vars = 0;
var_t no_of_clauses = 0;
cl_t assgn_vars;
var_t heuristic = 0;
var_t active_cls = 0;
var_t active_vars = 0;
bool unsat_bit = false;  // assignment: 0 = FALSE, 1 = TRUE
clv_t unit_cls;
cld_t pos_var_cnt;
cld_t neg_var_cnt;
cld_t pos_wbh_score;
cld_t neg_wbh_score;
cld_t kappa;
std::string fname;
std::string tmp_filename;
unsigned long long nano_time;

std::random_device rd;
std::mt19937 gen(rd());
std::uniform_real_distribution<> dis(
    0, 2);  // uniform distribution between 0 and 1

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

// -- Decison heuristic implementation ----
void max_sat_cls(lit_t l) {
  if (l > 0)
    ++pos_var_cnt[std::abs(l)];
  else
    ++neg_var_cnt[std::abs(l)];
}

void jeroslow_wang(lit_t l, var_t size) {
  if (l > 0) {
    pos_var_cnt[std::abs(l)] += 1.0 / pow(2, size);
  } else {
    neg_var_cnt[std::abs(l)] += 1.0 / pow(2, size);
  }
}

void kappa_crh_value(var_t size) {
  if (size == 0 || size > kappa.size()) {
    std::exit(code(Error::kappa_size_err));
  }
  switch (size) {
    case 1:
      kappa[1] = 1;  // fakely created
      break;
    case 2:
      kappa[2] = 1;
      break;
    case 3:
      kappa[3] = 0.2;
      break;
    case 4:
      kappa[4] = 0.05;
      break;
    case 5:
      kappa[5] = 0.01;
      break;
    case 6:
      kappa[6] = 0.003;
      break;
    default:
      kappa[size] = 20.4514 * pow(0.218673, size);
  }
}

void kappa_wbh_value(var_t size) {
  if (size == 0 || size > kappa.size()) {
    std::exit(code(Error::kappa_size_err));
  }
  kappa[size] = pow(5, 3 - size);
}

// The index of the kappa is the size of the clause - 1
// Similarly the size passed is the clause size - 1
void crh_lookahead(lit_t l, var_t size) {
  if (kappa[size] == 0) {
    kappa_crh_value(size);
  }
  if (l > 0) {
    neg_var_cnt[std::abs(l)] += kappa[size];
  } else {
    pos_var_cnt[std::abs(l)] += kappa[size];
  }
}

// Requires serious debugging
void wbh_find2_lit(var_t v, var_t c1, lit_t &lit_1, lit_t &lit_2) {
  lit_t head_lit = cnf_clauses[c1].literals[cnf_clauses[c1].head_ctr];
  lit_t tail_lit = cnf_clauses[c1].literals[cnf_clauses[c1].tail_ctr];
  if (v != std::abs(head_lit) && v != std::abs(tail_lit)) {
    lit_1 = head_lit;
    lit_2 = tail_lit;
  } else if (v == std::abs(head_lit)) {
    lit_2 = tail_lit;
    for (var_t pos = cnf_clauses[c1].head_ctr + 1;
         pos < cnf_clauses[c1].tail_ctr; ++pos) {
      if (cnf_variables[std::abs(cnf_clauses[c1].literals[pos])].active ==
          false) {
        continue;
      }
      lit_1 = cnf_clauses[c1].literals[pos];
      break;
    }
  } else if (v == std::abs(tail_lit)) {
    lit_1 = head_lit;
    for (var_t pos = cnf_clauses[c1].tail_ctr - 1;
         pos > cnf_clauses[c1].head_ctr; --pos) {
      if (cnf_variables[std::abs(cnf_clauses[c1].literals[pos])].active ==
          false) {
        continue;
      }
      lit_2 = cnf_clauses[c1].literals[pos];
      break;
    }
  } else {
    std::exit(code(Error::var_notin_clause));
  }
}

// --- Helper function for wbh heuristic ---
var_t wbf_per_lit(lit_t lit) {
  var_t var_score = 0;
  var_t size = 0;
  cl_t cls_occ;
  if (lit > 0)
    cls_occ = cnf_variables[std::abs(lit)].pos_occ_cls;
  else if (lit < 0)
    cls_occ = cnf_variables[std::abs(lit)].neg_occ_cls;
  for (var_t c : cls_occ) {
    if (cnf_clauses[c].active != 1) continue;
    size = cnf_clauses[c].size;
    if (kappa[size] == 0) {
      kappa_wbh_value(size);
    }
    var_score += kappa[size];
  }
  return var_score;
}

var_t wbh_score(lit_t lit_1, lit_t lit_2) {
  var_t score = 0;
  lit_1 *= -1;
  lit_2 *= -1;

  // TODO: Avoid calling wbh_per_lit if the literal do not occur in the clause
  if (lit_1 > 0) {
    if (pos_wbh_score[lit_1] == 0) {
      pos_wbh_score[lit_1] = wbf_per_lit(lit_1);
    }
    score += pos_wbh_score[lit_1];
  } else {
    if (neg_wbh_score[std::abs(lit_1)] == 0) {
      neg_wbh_score[std::abs(lit_1)] = wbf_per_lit(lit_1);
    }
    score += neg_wbh_score[std::abs(lit_1)];
  }
  if (lit_2 > 0) {
    if (pos_wbh_score[lit_2] == 0) {
      pos_wbh_score[lit_2] = wbf_per_lit(lit_2);
    }
    score += pos_wbh_score[lit_2];
  } else {
    if (neg_wbh_score[std::abs(lit_2)] == 0) {
      neg_wbh_score[std::abs(lit_2)] = wbf_per_lit(lit_2);
    }
    score += neg_wbh_score[std::abs(lit_2)];
  }
  return score;
}

// TODO: Avoid recalculating the score of the assigned var
void wbh_lookahead() {
  lit_t lit_1 = 0, lit_2 = 0;
  var_t score = 0;
  std::fill(pos_wbh_score.begin(), pos_wbh_score.end(), 0);
  std::fill(neg_wbh_score.begin(), neg_wbh_score.end(), 0);
  for (var_t v = 1; v < cnf_variables.size(); ++v) {
    if (cnf_variables[v].active == false) continue;

    for (var_t c1 : cnf_variables[v].pos_occ_cls) {
      if (cnf_clauses[c1].active != 1 || cnf_clauses[c1].size != 3) continue;
      wbh_find2_lit(v, c1, lit_1, lit_2);
      if (lit_1 == 0 || lit_2 == 0) continue;
      score = wbh_score(lit_1, lit_2);
      // assert(score > 0);
      neg_var_cnt[v] += score;
    }

    for (var_t c2 : cnf_variables[v].neg_occ_cls) {
      if (cnf_clauses[c2].active != 1 || cnf_clauses[c2].size != 3) continue;
      wbh_find2_lit(v, c2, lit_1, lit_2);
      if (lit_1 == 0 || lit_2 == 0) continue;
      score = wbh_score(lit_1, lit_2);
      // assert(score > 0);
      pos_var_cnt[v] += score;
    }
  }
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
inline cl_t extract_int(std::string line, var_t cls_id) {
  lit_t found;
  cl_t vec_int;
  std::stringstream ss;
  std::string temp;

  ss << line;
  while (!ss.eof()) {
    ss >> temp;
    if (std::stringstream(temp) >> found) {
      if (found == 0) break;
      if (found > INT_MAX) std::exit(code(Error::variable_value));
      if (heuristic == 0) max_sat_cls(found);
      if (found > 0)
        cnf_variables[std::abs(found)].pos_occ_cls.push_back(cls_id);
      else
        cnf_variables[std::abs(found)].neg_occ_cls.push_back(cls_id);
      vec_int.push_back(found);
    }
  }
  return vec_int;
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
      if (found > INT_MAX) std::exit(code(Error::variable_value));
      vec_int.push_back(found);
    }
  }
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

void ReadDimacs(const std::string filename) {
  fname = getFileName(filename);
  std::ifstream fin(filename);
  if (!fin.is_open()) {
    perror(("c Error while opening file " + filename).c_str());
    std::exit(code(Error::file_reading));
  }
  bool p_line = false;
  var_t num_original_clauses = 0;
  var_t biggest_cls_size = 0;
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

        active_vars = no_of_vars;
        active_cls = no_of_clauses;

        // Use one based indexing
        cnf_variables.resize(no_of_vars + 1);
        pos_var_cnt.resize(no_of_vars + 1);
        neg_var_cnt.resize(no_of_vars + 1);

        // std::cout << "c\nc Found 'p cnf " << no_of_vars << ' ' <<
        // no_of_clauses
        //<< "' header. \n";
        break;
      }
      default: {
        if (p_line == false) {
          std::exit(code(Error::file_pline));
        }
        cl_t clause = extract_int(line, num_original_clauses);
        // Push the clause in the cnf_clauses
        Clause *cls = new Clause;
        cls->active = 1;
        cls->literals = clause;
        cls->size = clause.size();
        cls->head_ctr = 0;
        cls->tail_ctr = clause.size() - 1;
        // tauto check implementation
        cnf_clauses.push_back(*cls);
        if (biggest_cls_size < clause.size()) {
          biggest_cls_size = clause.size();
        }
        if (clause.size() == 1) unit_cls.push_back(num_original_clauses);
        num_original_clauses++;
        break;
      }
    }
  }

  // --- Lookahead clause reduction Heuristic -------
  if (heuristic == 2) {
    kappa.resize(biggest_cls_size);
  }

  // --- Lookahead weighted binary Heuristic -------
  if (heuristic == 3) {
    kappa.resize(biggest_cls_size + 1);
    pos_wbh_score.resize(no_of_vars + 1);
    neg_wbh_score.resize(no_of_vars + 1);
  }

  if (heuristic == 4) {
    fname = getFileName(filename);
    nano_time = std::chrono::duration_cast<std::chrono::nanoseconds>(
                    std::chrono::system_clock::now().time_since_epoch())
                    .count();
    tmp_filename = "/tmp/" + std::to_string(nano_time) + fname;
    std::ifstream src(filename, std::ios::binary);
    std::ofstream dst(tmp_filename, std::ios::binary);
    dst << src.rdbuf();
  }
}

// --- Decision Hueristics for the variable selection ---
var_t VariableSelection() {
  var_t top_var = 0;
  var_t top_var_cnt =
      0;  // be careful be update it when change the heuristic val
  var_t max_pol;
  assert(pos_var_cnt.size() == neg_var_cnt.size());
  for (var_t var = 1; var < pos_var_cnt.size(); ++var) {
    if (cnf_variables[var].active == false) continue;
    max_pol = pos_var_cnt[var] * neg_var_cnt[var];
    if (max_pol < top_var_cnt) {
      continue;
    } else {
      top_var_cnt = max_pol;
      top_var = var;
    }
  }
  return top_var;
}

var_t pick_random_phase() { return dis(gen); }

// -- Update Data Structure based on the chosen decision variable ---
std::string DataStructureUpdate(lit_t dvar) {
  cl_t sat_cls_set, unsat_cls_set;
  if (dvar == 0) std::exit(code(Error::variable_value));
  if (cnf_variables[std::abs(dvar)].active == false) {
    return "NONE";
  }
  cnf_variables[std::abs(dvar)].active = false;
  assert(active_vars > 0);
  --active_vars;
  if (dvar > 0) {
    sat_cls_set = cnf_variables[std::abs(dvar)].pos_occ_cls;
    unsat_cls_set = cnf_variables[std::abs(dvar)].neg_occ_cls;
  } else {
    sat_cls_set = cnf_variables[std::abs(dvar)].neg_occ_cls;
    unsat_cls_set = cnf_variables[std::abs(dvar)].pos_occ_cls;
  }
  for (var_t c : sat_cls_set) {
    if (cnf_clauses[c].active == 0) {
      continue;
    }
    if (cnf_clauses[c].active == 1) {
      assert(active_cls > 0);
      --active_cls;
    }
    cnf_clauses[c].active = 0;
  }
  // Implemet early exit based on number of clauses/ i.e active_cls == 0
  if (active_cls == 0) {
    if (heuristic < 4) {
      formula_is_sat();
    } else {
      unsat_bit = true;
      return "UNSAT";
    }
  }

  dvar *= -1;
  for (var_t c : unsat_cls_set) {
    if (cnf_clauses[c].active == 0) {
      continue;
    }
    var_t hdptr = cnf_clauses[c].head_ctr;
    var_t tlptr = cnf_clauses[c].tail_ctr;

    // Single var UNSAT case
    if (hdptr == tlptr) {
      assert(cnf_clauses[c].literals[hdptr] == dvar);
      assert(cnf_clauses[c].literals[tlptr] == dvar);
      unsat_bit = true;
      return "UNSAT";
    }
    assert(hdptr < tlptr);
    // Two or more variable case
    if (cnf_clauses[c].literals[hdptr] == dvar) {
      while (
          cnf_variables[std::abs(
                            cnf_clauses[c].literals[cnf_clauses[c].head_ctr])]
              .active == false) {
        ++cnf_clauses[c].head_ctr;
      }

    } else if (cnf_clauses[c].literals[tlptr] == dvar) {
      while (
          cnf_variables[std::abs(
                            cnf_clauses[c].literals[cnf_clauses[c].tail_ctr])]
              .active == false) {
        --cnf_clauses[c].tail_ctr;
      }
    }
    assert(cnf_clauses[c].head_ctr <= cnf_clauses[c].tail_ctr);
    --cnf_clauses[c].size;
    if (cnf_clauses[c].head_ctr == cnf_clauses[c].tail_ctr) {
      unit_cls.push_back(c);
    }
  }
  if (active_cls == 0) formula_is_sat();
  return "NONE";
}

// --- Update Variable Stats ---
void UpdateVarStat(var_t heuristic) {
  // Clear all the variable statistics of the previous iteration
  std::fill(pos_var_cnt.begin(), pos_var_cnt.end(), 0);
  std::fill(neg_var_cnt.begin(), neg_var_cnt.end(), 0);
  // Recalculate the statistics again going over all the clauses -- Heuristics
  // TODO: Avoid going over all clauses again and just have avtive clauses
  // TODO: Delete those clauses and variables which inactive : Save space
  var_t total_active_cls = 0;
  if (heuristic == 3) {
    wbh_lookahead();
    return;
  }
  for (var_t i = 0; i < cnf_clauses.size(); ++i) {
    if (cnf_clauses[i].active != 1) {
      continue;
    } else {
      ++total_active_cls;
      var_t size = cnf_clauses[i].size;
      var_t elem_cnt = 0;
      for (var_t j = cnf_clauses[i].head_ctr; j <= cnf_clauses[i].tail_ctr;
           ++j) {
        lit_t l = cnf_clauses[i].literals[j];
        if (cnf_variables[std::abs(l)].active == false) continue;
        ++elem_cnt;
        if (heuristic == 0) {  // Maximum satisfying clause
          max_sat_cls(l);
        } else if (heuristic == 1) {  // Jeroslow Wang
          jeroslow_wang(l, size);
        } else if (heuristic == 2) {
          crh_lookahead(l, size - 1);
        } else if (heuristic >= 4) {
          jeroslow_wang(l, size);
          //max_sat_cls(l);
        }
      }
      assert(elem_cnt == size);
    }
  }
  if (total_active_cls == 0) {
    formula_is_sat();
  }
}

void RewriteInputFile() {
  std::ofstream fout(tmp_filename);
  if (!fout) {
    std::exit(code(Error::file_reading));
  }
  // Writing the cnf output in dimacs format
  fout << "p cnf " << no_of_vars << " " << active_cls << "\n";
  for (var_t i = 0; i < cnf_clauses.size(); ++i) {
    if (cnf_clauses[i].active == 0) {
      continue;
    } else {
      for (var_t j = cnf_clauses[i].head_ctr; j <= cnf_clauses[i].tail_ctr;
           ++j) {
        lit_t l = cnf_clauses[i].literals[j];
        if (cnf_variables[std::abs(l)].active == false) continue;
        fout << l << " ";
      }
      fout << "0"
           << "\n";
    }
  }
  fout.close();
}

// -- UCP : Unit Constraint Propagation ----
void UnitPropagation(var_t c) {
  var_t hdctr;
  assert(unit_cls.size() > 0);
  unit_cls.pop_back();
  hdctr = cnf_clauses[c].head_ctr;
  assert(hdctr == cnf_clauses[c].tail_ctr);
  if (DataStructureUpdate(cnf_clauses[c].literals[hdctr]) == "UNSAT") {
    unsat_bit = true;
    unit_cls.clear();
  }
}

std::string UnitConstraintPropogation() {
  bool ut = 0;
  if (unit_cls.size() > 0) ut = 1;
  while (unit_cls.size() > 0) {
    var_t cls = unit_cls[unit_cls.size() - 1];
    UnitPropagation(cls);
  }
  if (unsat_bit == true) return "UNSAT";
  if (heuristic < 4) {
    UpdateVarStat(heuristic);
  } else {
    if (assgn_vars.size() > 0 || ut == 1) RewriteInputFile();
  }
  return "NONE";
}

// --------  Update Clause Activity based on the Max Rebamable Horn ---
std::string ClauseActivityUpdate() {
  // std::string fname = getFileName(filename);
  std::string sat_out = "/tmp/" + std::to_string(nano_time) + fname + ".out";
  std::string cmd("../MaxSatRHorn.py -i ");
  cmd += tmp_filename;
  cmd += " -m 3";
  cmd += " > ";
  cmd += sat_out;
  std::future<int> future = std::async(std::launch::async, [=]() {
    auto retVal = system(cmd.c_str());
    return retVal;
  });

  cl_t cls_assgn;
  // std::cout << "c Running Max Renamable Horn solving ... "
  //          << "\nc\n";
  std::future_status status;

  status = future.wait_for(std::chrono::seconds(3000));

  // Handle timout and chek for the MemoryOut
  if (status == std::future_status::timeout) {
    std::cout << "c TimeOut! \n";
    std::terminate();
  }

  if (status == std::future_status::ready) {
    std::string filenm = sat_out;
    std::string line;
    std::ifstream file(filenm);
    cl_t cls_model;
    if (!file.is_open()) {
      perror(("c Error while opening file " + filenm).c_str());
      std::exit(code(Error::file_reading));
    }
    while (std::getline(file, line)) {
      if (line[0] == 'S') {
        unsat_bit = true;
        return "UNSAT";
      } else if (line[0] == 'E') {
        std::cout << "c Error in the MaxSAT call of rhorn. Exiting.\n";
        std::exit(0);
      } else {
        cls_model = extract_jint(line);
      }
      break;
    }
    var_t non_horn_cls = 0;
    var_t cls_index = 0;
    for (var_t i = 0; i < cls_model.size(); ++i) {
      while (cnf_clauses[cls_index].active == 0) {
        ++cls_index;
      }
      if (cls_model[i] < 0) {
        cnf_clauses[cls_index].active = 2;
        assert(active_cls > 0);
        --active_cls;
      } else {
        ++non_horn_cls;
      }
      ++cls_index;
    }
    // assert(cls_index == no_of_clauses);
    if (non_horn_cls == 0) {
      unsat_bit = true;
      return "UNSAT";
    }
  }

  const int r1 = remove(sat_out.c_str());
  if (r1 != 0) {
    printf("c unable to removed the temp file.\n");
  }
  UpdateVarStat(heuristic);
  return "NONE";
}  // namespace

// -- Write the input file for the next MAXSAT call ---
void InputFileUpdate() {
  while (unit_cls.size() > 0) {
    var_t cls = unit_cls[unit_cls.size() - 1];
    UnitPropagation(cls);
  }
  if (unsat_bit == true) return;

  // Reset the clauses last time added to the MAXSAT call
  var_t horn_cls_cnt = 0;
  var_t sat_cls_cnt = 0;
  for (var_t c = 0; c < cnf_clauses.size(); ++c) {
    if (cnf_clauses[c].active == 2) {
      cnf_clauses[c].active = 1;
      ++horn_cls_cnt;
    } else if (cnf_clauses[c].active == 1) {
      ++sat_cls_cnt;
    }
  }
  assert(active_cls == sat_cls_cnt);
  active_cls = horn_cls_cnt + sat_cls_cnt;
}

// --- Parse Commandline argument ---
void show_usage() noexcept {
  std::cout << "Decision-Heuristics [version 0.0.1]. (C) Copyright 2020 "
               "\nUsage: ./decision_heuristics [filename] [heuristic: 0 (max "
               "satisfiable clause), 1 (Jeoslow Wang), "
               "2 (crh_lookahead), 3 (wbh Lookahead), 4 (Rhorn MaxSAT)]\n";
  std::exit(0);
}

// --- Printing basic information about the tool ---
static void banner() {
  std::cout << "c WaterMellon SAT Solver based on RHorn Heuristic.\n"
               "c Version: "
            << version
            << "\nc Copyright (c) 2020 Johannes Kepler University.\n";
}

// --- Print Output --- //
void output(const std::string filename) {
  // std::cout << "c\nc Program information:\n";
  // std::cout << "c The Tree height is: " << assgn_vars.size() << "\n";
  std::cout << "c " << fname << " " << assgn_vars.size() << "\n";
  std::exit(0);
}

}  // namespace

int main(const int argc, const char *const argv[]) {
  if (argc == 1 || argc > 3) {
    std::cout << "Invalid number of arguments.\n";
    std::exit(code(Error::invalid_args_count));
  }
  const std::string filename = argv[1];
  if (argc == 3) {
    heuristic = std::stoi(argv[2]);
  }
  if (filename == "-v" or filename == "--version") version_information();
  if (filename == "-h" or filename == "--help") show_usage();
  banner();
  ReadDimacs(filename);
  while (!unsat_bit) {
    if (UnitConstraintPropogation() == "UNSAT") break;
    if (heuristic == 4)
      if (ClauseActivityUpdate() == "UNSAT") break;
    lit_t decision_var = VariableSelection();
    if (decision_var == 0) std::exit(code(Error::decision_error));
    // TODO: Check how good this random function is
    if (pick_random_phase()) {
      decision_var *= -1;
    }
    assgn_vars.push_back(decision_var);
    if (DataStructureUpdate(decision_var) == "UNSAT") break;
    assert(assgn_vars.size() <= no_of_vars);
    if (heuristic == 4) InputFileUpdate();
  }
  output(filename);
  return 0;
}
