// --- Includes ----------------------------------------------------------------

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <list>
#include <map>
#include <string>
#include <utility>

// --- Types and constants -----------------------------------------------------

typedef uint32_t variable_t;
typedef enum { POSITIVE, NEGATIVE } polarity_t;
typedef std::pair<polarity_t, variable_t> literal_t;

typedef uint32_t index_t;
typedef std::list<literal_t> clause_t;
typedef std::map<index_t, clause_t> formula_t;

typedef std::list<index_t> indices_t;

typedef struct {
    indices_t indices;
} delete_t;

typedef std::list<index_t> rups_t;
typedef std::list<std::pair<index_t, rups_t>> rats_t;

typedef struct {
    index_t index;
    clause_t clause;
    bool empty;
    rups_t rups;
    rats_t rats;
} extend_t;

typedef enum { DELETE, EXTEND } type_t;

typedef struct {
    type_t type;
    delete_t delete_;
    extend_t extend;
} step_t;

typedef enum { DONE, MORE, FAIL } result_t;
typedef std::pair<size_t, clause_t> sz_clause_t;

#define DEBUG 0

// --- Macros and inline functions ---------------------------------------------

// --- Globals -----------------------------------------------------------------

static variable_t g_n_vars;
static index_t g_n_clauses;
static formula_t g_f;

// --- Helper declarations -----------------------------------------------------

#if DEBUG > 0
static void dump_clause(const std::string &label, const clause_t &c);
#endif
static bool read_formula(const char *path);
static bool read_header(std::ifstream &ifs);
static bool read_body(std::ifstream &ifs);
static literal_t make_literal(int64_t val);
static literal_t flip_literal(const literal_t &l);
static bool check_proof(const char *path);
static bool read_step(step_t &s, std::ifstream &ifs);
static bool read_delete(step_t &s, std::ifstream &ifs);
static bool read_extend(step_t &s, index_t i, int64_t val, std::ifstream &ifs);
static bool read_clause(clause_t &c, int64_t &val, std::ifstream &ifs);
static bool read_rup(rups_t &rups, int64_t &val, std::ifstream &ifs);
static bool read_rat(rats_t &rats, int64_t &val, std::ifstream &ifs);
static bool run_step(const step_t &s);
static bool run_delete(const delete_t &dp);
static bool run_extend(const extend_t &ep);
static result_t check_rup(clause_t &c, const rups_t &rups);
static sz_clause_t minus(const clause_t &c1, const clause_t &c2);

// --- API ---------------------------------------------------------------------

int main(int argc, char *argv[])
{
    if (argc != 3) {
        std::cerr << "usage: rewrite formula-file lrat-file" << std::endl;
        return 1;
    }

    if (!read_formula(argv[1]) || !check_proof(argv[2])) {
        return 1;
    }

    return 0;
}

// --- Helpers -----------------------------------------------------------------

#if DEBUG > 0
static void dump_clause(const std::string &label, const clause_t &c)
{
    std::cout << label;

    for (auto it = c.cbegin(); it != c.cend(); ++it) {
        std::cout << (it->first == POSITIVE ? " " : " -");
        std::cout << it->second;
    }

    std::cout << std::endl;
}
#endif

static bool read_formula(const char *path)
{
    std::ifstream ifs(path, std::ifstream::in);

    if (!ifs.is_open()) {
        std::cerr << "failed to open formula file " << path << std::endl;
        return false;
    }

    if (!read_header(ifs) || !read_body(ifs)) {
        return false;
    }

    return true;
}

static bool read_header(std::ifstream &ifs)
{
    std::string token;

    if (!(ifs >> token) || token != "p" ||
            !(ifs >> token) || token != "cnf" ||
            !(ifs >> g_n_vars) ||
            !(ifs >> g_n_clauses)) {
        std::cerr << "invalid header" << std::endl;
        return false;
    }

    return true;
}

static bool read_body(std::ifstream &ifs)
{
    index_t i = 0;
    clause_t c;
    int64_t val;

    while (ifs >> val) {
        if (val == 0) {
            g_f.insert(std::make_pair(++i, c));
            c.clear();
        }
        else {
            literal_t l = make_literal(val);
            c.push_back(l);
        }
    }

    if (!ifs.eof() || val != 0) {
        std::cerr << "invalid body" << std::endl;
        return false;
    }

    return true;
}

static literal_t make_literal(int64_t val)
{
    return val < 0 ?
        std::make_pair(NEGATIVE, (variable_t)-val) :
        std::make_pair(POSITIVE, (variable_t)val);
}

static literal_t flip_literal(const literal_t &l)
{
    return l.first == POSITIVE ?
        std::make_pair(NEGATIVE, l.second) :
        std::make_pair(POSITIVE, l.second);
}

static bool check_proof(const char *path)
{
    std::ifstream ifs(path, std::ifstream::in);

    if (!ifs.is_open()) {
        std::cerr << "failed to open proof file " << path << std::endl;
        return false;
    }

    while (true) {
        step_t s;

        if (!read_step(s, ifs) || !run_step(s)) {
            return false;
        }

        if (s.type == EXTEND && s.extend.empty) {
            return true;
        }
    }
}

static bool read_step(step_t &s, std::ifstream &ifs)
{
    index_t i;
    std::string str;

    if (!(ifs >> i) || !(ifs >> str)) {
        std::cerr << "invalid step" << std::endl;
        return false;
    }

    if (str == "d") {
        return read_delete(s, ifs);
    }
    else {
        int64_t val = strtoll(str.c_str(), NULL, 10);
        return read_extend(s, i, val, ifs);
    }
}

static bool read_delete(step_t &s, std::ifstream &ifs)
{
    s.type = DELETE;
    delete_t &dp = s.delete_;
    index_t i;

    while (ifs >> i) {
        if (i == 0) {
            return true;
        }

        dp.indices.push_back(i);
    }

    std::cerr << "invalid delete step" << std::endl;
    return false;
}

static bool read_extend(step_t &s, index_t i, int64_t val, std::ifstream &ifs)
{
    s.type = EXTEND;
    extend_t &ep = s.extend;
    ep.index = i;
    ep.empty = val == 0;

    return read_clause(ep.clause, val, ifs) &&
            read_rup(ep.rups, val, ifs) &&
            (val == 0 || read_rat(ep.rats, val, ifs));
}

static bool read_clause(clause_t &c, int64_t &val, std::ifstream &ifs)
{
    while (val != 0) {
        literal_t l = make_literal(val);
        c.push_back(l);

        if (!(ifs >> val)) {
            std::cerr << "invalid clause" << std::endl;
            return false;
        }
    }

    return true;
}

static bool read_rup(rups_t &rups, int64_t &val, std::ifstream &ifs)
{
    while (true) {
        if (!(ifs >> val)) {
            std::cerr << "invalid RUP hints" << std::endl;
            return false;
        }

        if (val <= 0) {
            return true;
        }

        rups.push_back((index_t)val);
    }
}

static bool read_rat(rats_t &rats, int64_t &val, std::ifstream &ifs)
{
    index_t i = (index_t)-val;
    rups_t rups;

    while (true) {
        if (!(ifs >> val)) {
            std::cerr << "invalid RAT hints" << std::endl;
            return false;
        }

        if (val > 0) {
            rups.push_back((index_t)val);
        }
        else {
            rats.push_back(std::make_pair(i, rups));

            if (val == 0) {
                return true;
            }

            i = (index_t)-val;
            rups.clear();
        }
    }
}

static bool run_step(const step_t &s)
{
    return s.type == DELETE ? run_delete(s.delete_) : run_extend(s.extend);
}

static bool run_delete(const delete_t &dp)
{
    const indices_t &indices = dp.indices;

    for (auto it = indices.cbegin(); it != indices.cend(); ++it) {
        if (g_f.erase(*it) == 0) {
            std::cerr << "invalid delete index " << *it << std::endl;
            return false;
        }
    }

    return true;
}

static bool run_extend(const extend_t &ep)
{
    clause_t c = ep.clause;

    switch (check_rup(c, ep.rups)) {
    case DONE:
        g_f.insert(std::make_pair(ep.index, ep.clause));
        return true;

    case FAIL:
        return false;

    case MORE:
        break;
    }

    std::cerr << "RAT not yet supported" << std::endl;
    return false;
}

static result_t check_rup(clause_t &c, const rups_t &rups)
{
    for (auto it1 = rups.cbegin(); it1 != rups.cend(); ++it1) {
        const auto it2 = g_f.find(*it1);

        if (it2 == g_f.end()) {
            std::cerr << "invalid RUP hint index " << *it1 << std::endl;
            return FAIL;
        }

        const auto &diff = minus(it2->second, c);

        if (diff.first == 0) {
            return DONE;
        }

        if (diff.first > 1) {
            std::cerr << "non-unit clause for RUP hint index " << *it1 <<
                    std::endl;
            return FAIL;
        }

        c.push_back(flip_literal(diff.second.front()));
    }

    return MORE;
}

static sz_clause_t minus(const clause_t &c1, const clause_t &c2)
{
    clause_t diff;
    size_t sz = 0;

    for (auto it = c1.cbegin(); it != c1.cend(); ++it) {
        if (std::find(c2.cbegin(), c2.cend(), *it) == c2.cend()) {
            diff.push_back(*it);
            ++sz;
        }
    }

    return std::make_pair(sz, diff);
}

