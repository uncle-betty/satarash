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

typedef std::list<index_t> rup_hints_t;
typedef std::list<std::pair<index_t, rup_hints_t>> rat_hints_t;

typedef struct {
    index_t index;
    clause_t clause;
    bool empty;
    rup_hints_t rup_hints;
    rat_hints_t rat_hints;
} extend_t;

typedef enum { DELETE, EXTEND } type_t;

typedef struct {
    type_t type;
    delete_t delete_;
    extend_t extend;
} step_t;

typedef enum { DONE, MORE, FAIL } result_t;

// --- Macros and inline functions ---------------------------------------------

// --- Globals -----------------------------------------------------------------

// --- Helper declarations -----------------------------------------------------

static void dump_clause(const std::string &label, const clause_t &c);
static bool read_formula(formula_t &f, variable_t &n_vars, index_t &n_clauses, const char *path);
static bool read_header(variable_t &n_vars, index_t &n_clauses, std::ifstream &ifs);
static bool read_body(formula_t &f, std::ifstream &ifs, variable_t n_vars, index_t n_clauses);
static bool make_literal(literal_t &l, int64_t val, variable_t n_vars);
static bool check_proof(formula_t &f, const char *path, variable_t n_vars);
static bool read_step(step_t &s, std::ifstream &ifs, variable_t n_vars);
static bool read_delete(step_t &s, std::ifstream &ifs);
static bool read_extend(step_t &s, index_t i, int64_t val, std::ifstream &ifs, variable_t n_vars);
static bool run_step(formula_t &f, const step_t &s);
static bool run_delete(formula_t &f, const delete_t &dp);
static bool run_extend(formula_t &f, const extend_t &ep);
static result_t check_rup(clause_t &c, const formula_t &f, const rup_hints_t &hs);
static std::pair<size_t, clause_t> minus(const clause_t &c1, const clause_t &c2);
static literal_t flip_literal(const literal_t &l);

// --- API ---------------------------------------------------------------------

int main(int argc, char *argv[])
{
    if (argc != 3) {
        std::cerr << "usage: rewrite formula-file lrat-file" << std::endl;
        return 1;
    }

    formula_t f;
    variable_t n_vars;
    index_t n_clauses;

    if (!read_formula(f, n_vars, n_clauses, argv[1]) ||
            !check_proof(f, argv[2], n_vars)) {
        return 1;
    }

    return 0;
}

// --- Helpers -----------------------------------------------------------------

static void dump_clause(const std::string &label, const clause_t &f)
{
    std::cout << label;

    for (auto it = f.cbegin(); it != f.cend(); ++it) {
        std::cout << (it->first == POSITIVE ? " " : " -");
        std::cout << it->second;
    }

    std::cout << std::endl;
}

static bool read_formula(formula_t &f, variable_t &n_vars, index_t &n_clauses,
        const char *path)
{
    std::ifstream ifs(path, std::ifstream::in);

    if (!ifs.is_open()) {
        std::cerr << "failed to open formula file " << path << std::endl;
        return false;
    }

    if (!read_header(n_vars, n_clauses, ifs) ||
            !read_body(f, ifs, n_vars, n_clauses)) {
        std::cerr << "failed to read formula" << std::endl;
        return false;
    }

    return true;
}

static bool read_header(variable_t &n_vars, index_t &n_clauses,
        std::ifstream &ifs)
{
    std::string token;

    if (!(ifs >> token) || token != "p") {
        std::cerr << "invalid header [1]" << std::endl;
        return false;
    }

    if (!(ifs >> token) || token != "cnf") {
        std::cerr << "invalid header [2]" << std::endl;
        return false;
    }

    if (!(ifs >> n_vars)) {
        std::cerr << "invalid header [3]" << std::endl;
        return false;
    }

    if (!(ifs >> n_clauses)) {
        std::cerr << "invalid header [4]" << std::endl;
        return false;
    }

    return true;
}

static bool read_body(formula_t &f, std::ifstream &ifs, variable_t n_vars,
        index_t n_clauses)
{
    index_t i = 0;
    clause_t c;
    int64_t val;

    while (ifs >> val) {
        if (val == 0) {
            f.insert(std::make_pair(++i, c));
            c.clear();
        }
        else {
            literal_t l;

            if (!make_literal(l, val, n_vars)) {
                return false;
            }

            c.push_back(l);
        }
    }

    if (!ifs.eof() || val != 0) {
        std::cerr << "invalid body" << std::endl;
        return false;
    }

    if (i != n_clauses) {
        std::cerr << "clause count mismatch: " << i << " vs. " << n_clauses <<
                std::endl;
        return false;
    }

    return true;
}

static bool make_literal(literal_t &l, int64_t val, variable_t n_vars)
{
    polarity_t pol;
    variable_t var;

    if (val < 0) {
        pol = NEGATIVE;
        var = (variable_t)-val;
    }
    else {
        pol = POSITIVE;
        var = (variable_t)val;
    }

    if (var == 0 || var > n_vars) {
        std::cerr << "invalid variable: " << var << " of " << n_vars <<
                std::endl;
        return false;
    }

    l.first = pol;
    l.second = var;
    return true;
}

static bool check_proof(formula_t &f, const char *path, variable_t n_vars)
{
    std::ifstream ifs(path, std::ifstream::in);

    if (!ifs.is_open()) {
        std::cerr << "failed to open proof file " << path << std::endl;
        return false;
    }

    while (true) {
        step_t s;

        if (!read_step(s, ifs, n_vars)) {
            std::cerr << "failed to read from proof file " << path << std::endl;
            return false;
        }

        if (!run_step(f, s)) {
            std::cerr << "failed to run proof step" << std::endl;
            return false;
        }

        if (s.type == EXTEND && s.extend.empty) {
            return true;
        }
    }
}

static bool read_step(step_t &s, std::ifstream &ifs, variable_t n_vars)
{
    index_t i;

    if (!(ifs >> i)) {
        std::cerr << "invalid step [1]" << std::endl;
        return false;
    }

    std::string str;

    if (!(ifs >> str)) {
        std::cerr << "invalid step [2]" << std::endl;
        return false;
    }

    if (str == "d") {
        return read_delete(s, ifs);
    }
    else {
        int64_t val = strtoll(str.c_str(), NULL, 10);
        return read_extend(s, i, val, ifs, n_vars);
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

static bool read_extend(step_t &s, index_t i, int64_t val, std::ifstream &ifs,
         variable_t n_vars)
{
    s.type = EXTEND;
    extend_t &ep = s.extend;
    ep.index = i;
    ep.empty = val == 0;

    while (val != 0) {
        literal_t l;

        if (!make_literal(l, val, n_vars)) {
            std::cerr << "invalid extend step [1]" << std::endl;
            return false;
        }

        ep.clause.push_back(l);

        if (!(ifs >> val)) {
            std::cerr << "invalid extend step [2]" << std::endl;
            return false;
        }
    }

    while (true) {
        if (!(ifs >> val)) {
            std::cerr << "invalid extend step [3]" << std::endl;
            return false;
        }

        if (val == 0) {
            return true;
        }

        if (val < 0) {
            break;
        }

        ep.rup_hints.push_back((index_t)val);
    }

    i = (index_t)-val;
    rup_hints_t hs;

    while (true) {
        if (!(ifs >> val)) {
            std::cerr << "invalid extend step [4]" << std::endl;
            return false;
        }

        if (val > 0) {
            hs.push_back((index_t)val);
            continue;
        }

        ep.rat_hints.push_back(std::make_pair(i, hs));

        if (val == 0) {
            return true;
        }

        i = (index_t)-val;
        hs.clear();
    }

    return false;
}

static bool run_step(formula_t &f, const step_t &s)
{
    switch (s.type) {
    case DELETE:
        return run_delete(f, s.delete_);

    case EXTEND:
        return run_extend(f, s.extend);

    default:
        assert(false);
    }
}

static bool run_delete(formula_t &f, const delete_t &dp)
{
    const indices_t &indices = dp.indices;

    for (auto it = indices.cbegin(); it != indices.cend(); ++it) {
        if (f.erase(*it) == 0) {
            std::cerr << "deleting with invalid index " << *it << std::endl;
            return false;
        }
    }

    return true;
}

static bool run_extend(formula_t &f, const extend_t &ep)
{
    clause_t c = ep.clause;

    switch (check_rup(c, f, ep.rup_hints)) {
    case DONE:
        f.insert(std::make_pair(ep.index, ep.clause));
        return true;

    case FAIL:
        return false;

    case MORE:
        break;
    }

    std::cerr << "RAT not yet supported" << std::endl;
    return false;
}

static result_t check_rup(clause_t &c, const formula_t &f,
        const rup_hints_t &hs)
{
    for (auto it1 = hs.cbegin(); it1 != hs.cend(); ++it1) {
        const auto it2 = f.find(*it1);

        if (it2 == f.end()) {
            std::cerr << "invalid RUP hint index " << *it1 << std::endl;
            return FAIL;
        }

        const auto &diff = minus(it2->second, c);

        if (diff.first == 0) {
            return DONE;
        }

        if (diff.first > 1) {
            std::cerr << "non-unit clause with RUP hint index " << *it1 <<
                    std::endl;
            return FAIL;
        }

        c.push_back(flip_literal(diff.second.front()));
    }

    return MORE;
}

static std::pair<size_t, clause_t> minus(const clause_t &c1, const clause_t &c2)
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

static literal_t flip_literal(const literal_t &l)
{
    switch (l.first) {
    case POSITIVE:
        return std::make_pair(NEGATIVE, l.second);

    case NEGATIVE:
        return std::make_pair(POSITIVE, l.second);
    }

    assert(false);
}
