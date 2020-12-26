// --- Includes ----------------------------------------------------------------

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <list>
#include <unordered_map>
#include <queue>
#include <string>
#include <utility>
#include <vector>

// --- Types and constants -----------------------------------------------------

typedef uint32_t variable_t;
typedef enum { POSITIVE, NEGATIVE } polarity_t;
typedef std::pair<polarity_t, variable_t> literal_t;

typedef uint32_t index_t;
typedef std::list<literal_t> clause_t;
typedef std::unordered_map<index_t, clause_t> formula_t;

typedef std::list<index_t> indices_t;

typedef struct {
    indices_t indices;
} delete_t;

typedef std::list<index_t> rups_t;
typedef std::list<std::pair<index_t, rups_t>> rats_t;

typedef struct {
    index_t index;
    clause_t clause;
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

typedef std::unordered_map<index_t, index_t> index_map_t;
template <class T> using min_heap_t =
        std::priority_queue<T, std::vector<T>, std::greater<T>>;
typedef min_heap_t<index_t> recycler_t;

#define DEBUG 0

// --- Macros and inline functions ---------------------------------------------

// --- Globals -----------------------------------------------------------------

static variable_t g_n_vars;
static index_t g_n_clauses = 0;
static formula_t g_f;
static uint32_t g_n_steps = 0;

static index_map_t g_index_map;
static recycler_t g_recycler;

// --- Helper declarations -----------------------------------------------------

#if DEBUG > 0
static void dump_clause(const std::string &label, const clause_t &c);
#endif
static bool read_formula(const char *path);
static bool read_header(std::ifstream &ifs);
static bool read_body(std::ifstream &ifs);
static literal_t make_lit(int64_t val);
static literal_t flip_lit(const literal_t &l);
static bool check_proof(const char *path);
static bool read_step(step_t &s, std::ifstream &ifs);
static bool read_delete(step_t &s, std::ifstream &ifs);
static bool read_extend(step_t &s, index_t i, int64_t val, std::ifstream &ifs);
static bool read_clause(clause_t &c, int64_t &val, std::ifstream &ifs);
static bool read_rup(rups_t &rups, int64_t &val, std::ifstream &ifs);
static bool read_rat(rats_t &rats, int64_t &val, std::ifstream &ifs);
static bool run_step(step_t &s);
static bool run_delete(const delete_t &dp);
static bool run_extend(extend_t &ep);
static index_t get_index(index_t i0);
static void put_index(index_t i0, index_t i);
static bool map_index(index_t &i);
static result_t check_rup(clause_t &c, const rups_t &rups);
static std::pair<size_t, clause_t> minus(const clause_t &c1, const clause_t &c2);
static bool check_rat(clause_t &c, rats_t &rats);
static bool check_clause_1(const clause_t &cf, const literal_t &not_l);
static bool check_clause_2(index_t i, const clause_t &cf, const clause_t &c, const literal_t &l, rats_t &rats);
static bool check_clause_3(index_t i, const clause_t &cf, const clause_t &c, const literal_t &not_l, rats_t &rats);
static bool validate_rats(index_t i, rats_t &rats);
static clause_t resolvent(const clause_t &c, const clause_t &cf, const literal_t &not_l);

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
    index_t dummy;

    if (!(ifs >> token) || token != "p" ||
            !(ifs >> token) || token != "cnf" ||
            !(ifs >> g_n_vars) || !(ifs >> dummy)) {
        std::cerr << "invalid header" << std::endl;
        return false;
    }

    return true;
}

static bool read_body(std::ifstream &ifs)
{
    index_t i0 = 0;
    clause_t c;
    int64_t val;

    while (ifs >> val) {
        if (val == 0) {
            index_t i = get_index(++i0);
            g_f.insert(std::make_pair(i, c));
            c.clear();
        }
        else {
            literal_t l = make_lit(val);
            c.push_back(l);
        }
    }

    if (!ifs.eof() || val != 0) {
        std::cerr << "invalid body" << std::endl;
        return false;
    }

    return true;
}

static literal_t make_lit(int64_t val)
{
    return val < 0 ?
        std::make_pair(NEGATIVE, (variable_t)-val) :
        std::make_pair(POSITIVE, (variable_t)val);
}

static literal_t flip_lit(const literal_t &l)
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

        if (s.type == EXTEND && s.extend.clause.empty()) {
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

    return read_clause(ep.clause, val, ifs) &&
            read_rup(ep.rups, val, ifs) &&
            (val == 0 || read_rat(ep.rats, val, ifs));
}

static bool read_clause(clause_t &c, int64_t &val, std::ifstream &ifs)
{
    while (val != 0) {
        literal_t l = make_lit(val);
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

static bool run_step(step_t &s)
{
    ++g_n_steps;

    bool ok = s.type == DELETE ? run_delete(s.delete_) : run_extend(s.extend);

    if (!ok) {
        std::cerr << "step " << g_n_steps << " failed" << std::endl;
        return false;
    }

    return true;
}

static bool run_delete(const delete_t &dp)
{
    const indices_t &indices = dp.indices;

    for (auto it = indices.cbegin(); it != indices.cend(); ++it) {
        index_t i = *it;

        if (!map_index(i)) {
            std::cerr << "invalid original delete index" << std::endl;
            return false;
        }

        if (g_f.erase(i) == 0) {
            std::cerr << "invalid delete index " << *it << " / " << i <<
                    std::endl;
            return false;
        }

        put_index(*it, i);
    }

    return true;
}

static bool run_extend(extend_t &ep)
{
    clause_t c = ep.clause;
    index_t i = get_index(ep.index);

    switch (check_rup(c, ep.rups)) {
    case DONE:
        g_f.insert(std::make_pair(i, ep.clause));
        return true;

    case FAIL:
        return false;

    case MORE:
        break;
    }

    if (check_rat(c, ep.rats)) {
        g_f.insert(std::make_pair(i, ep.clause));
        return true;
    }

    return false;
}

static index_t get_index(index_t i0)
{
    index_t i;

    if (!g_recycler.empty()) {
        i = g_recycler.top();
        g_recycler.pop();
    }
    else {
        i = ++g_n_clauses;
    }

    g_index_map.insert(std::make_pair(i0, i));
    return i;
}

static void put_index(index_t i0, index_t i)
{
    g_index_map.erase(i0);
    g_recycler.push(i);
}

static bool map_index(index_t &i)
{
    auto it = g_index_map.find(i);

    if (it == g_index_map.end()) {
        std::cerr << "failed to map index " << i << std::endl;
        return false;
    }

    i = it->second;
    return true;
}

static result_t check_rup(clause_t &c, const rups_t &rups)
{
    for (auto it1 = rups.cbegin(); it1 != rups.cend(); ++it1) {
        index_t i = *it1;

        if (!map_index(i)) {
            std::cerr << "invalid original RUP hint index" << std::endl;
            return FAIL;
        }

        const auto it2 = g_f.find(i);

        if (it2 == g_f.end()) {
            std::cerr << "invalid RUP hint index " << *it1 << " / " << i <<
                    std::endl;
            return FAIL;
        }

        const auto &diff = minus(it2->second, c);

        if (diff.first == 0) {
            return DONE;
        }

        if (diff.first > 1) {
            std::cerr << "non-unit clause for RUP hint index " << *it1 <<
                    " / " << i << std::endl;
            return FAIL;
        }

        c.push_back(flip_lit(diff.second.front()));
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

static bool check_rat(clause_t &c, rats_t &rats)
{
    if (c.empty()) {
        std::cerr << "RAT check with empty clause" << std::endl;
        return false;
    }

    literal_t l = c.front();
    literal_t not_l = flip_lit(l);

    for (auto it = g_f.cbegin(); it != g_f.cend(); ++it) {
        index_t i = it->first;
        const clause_t &cf = it->second;

        if (!check_clause_1(cf, not_l) &&
                !check_clause_2(i, cf, c, l, rats) &&
                !check_clause_3(i, cf, c, not_l, rats)) {
            return false;
        }
    }

    return true;
}

static bool check_clause_1(const clause_t &cf, const literal_t &not_l)
{
    return std::find(cf.cbegin(), cf.cend(), not_l) == cf.cend();
}

static bool check_clause_2(index_t i, const clause_t &cf, const clause_t &c,
        const literal_t &l, rats_t &rats)
{
    // it's ok for |c| and |cf| to contain |not_l| and |l|, respectively, as
    // it makes both clauses tautologies:
    //   - |l| is |c|'s first literal by definition
    //   - |not_l| is in |cf| since we passed check_clause_1()
    for (auto it = c.cbegin(); it != c.cend(); ++it) {
        if (*it != l &&
                std::find(cf.cbegin(), cf.cend(), flip_lit(*it)) != cf.cend()) {
            if (!validate_rats(i, rats)) {
                return false;
            }

            rups_t &rups = rats.front().second;

            if (!rups.empty()) {
                std::cerr << "non-empty RUP hints" << std::endl;
                return false;
            }

            rats.pop_front();
            return true;
        }
    }

    return false;
}

static bool check_clause_3(index_t i, const clause_t &cf, const clause_t &c,
        const literal_t &not_l, rats_t &rats)
{
    if (!validate_rats(i, rats)) {
        return false;
    }

    clause_t &&cr = resolvent(c, cf, not_l);
    rups_t &rups = rats.front().second;

    if (check_rup(cr, rups) != DONE) {
        std::cerr << "resolvent RUP check failed for index " << i << std::endl;
        return false;
    }

    rats.pop_front();
    return true;
}

static bool validate_rats(index_t i, rats_t &rats)
{
    if (rats.empty()) {
        std::cerr << "no RAT hint left for index " << i << std::endl;
        return false;
    }

    auto &rat = rats.front();
    index_t k = rat.first;

    if (!map_index(k)) {
        std::cerr << "invalid original RAT hint index" << std::endl;
        return false;
    }

    if (k != i) {
        std::cerr << "invalid RAT hint index: " << rat.first << " / " << k <<
                " vs. " << i << std::endl;
        return false;
    }

    return true;
}

static clause_t resolvent(const clause_t &c, const clause_t &cf,
        const literal_t &not_l)
{
    clause_t res = c;

    for (auto it = cf.cbegin(); it != cf.cend(); ++it) {
        if (*it != not_l) {
            res.push_back(*it);
        }
    }

    return res;
}
