// --- Includes ----------------------------------------------------------------

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <queue>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

// --- Types and constants -----------------------------------------------------

typedef uint32_t variable_t;
typedef enum { POSITIVE, NEGATIVE } polarity_t;
typedef std::pair<polarity_t, variable_t> literal_t;

typedef uint32_t index_t;
typedef std::vector<literal_t> literals_t;
typedef literals_t clause_t;
// ordered map - traversal must be in index order
typedef std::map<index_t, clause_t> formula_t;

typedef std::vector<index_t> indices_t;

typedef struct {
    indices_t indices;
} delete_t;

typedef std::vector<index_t> rups_t;
typedef std::pair<index_t, rups_t> rat_t;
typedef std::vector<rat_t> rats_t;

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

static variable_t g_n_vars = 0;
static index_t g_n_clauses = 0;
static formula_t g_f;
static uint32_t g_n_steps = 0;

static index_map_t g_index_map;
static recycler_t g_recycler;

static uint32_t g_bits_v;
static uint32_t g_bits_c;

// --- Helper declarations -----------------------------------------------------

#if DEBUG > 0
static void show_binary(uint32_t val, uint32_t n_bits);
static void show_clause(const clause_t &c);
static void show_formula(void);
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
static bool remap_step(step_t &s);
static bool remap_delete(delete_t &dp);
static bool remap_extend(extend_t &ep);
static index_t get_index(index_t i0);
static void put_index(index_t i0, index_t i);
static bool map_index(index_t &i);
static bool run_step(const step_t &s);
static bool run_delete(const delete_t &dp);
static bool run_extend(const extend_t &ep);
static result_t check_rup(clause_t &c, const rups_t &rups);
static std::pair<size_t, clause_t> minus(const clause_t &c1, const clause_t &c2);
static bool check_rat(clause_t &c, const rats_t &rats);
static bool needs_check(const clause_t &cf, const literal_t &not_l);
static bool validate_rats(const rats_t &rats, uint32_t i_rat, index_t i);
static bool check_rat_rup(const clause_t &cf, const clause_t &c, const literal_t &l, const literal_t &not_l, const rat_t &rat);
static bool check_clause_1(const clause_t &cf, const clause_t &c, const literal_t &l);
static bool check_clause_2(const clause_t &cf, const clause_t &c, const literal_t &l, const literal_t &not_l, const rups_t &rups);
static clause_t resolvent(const clause_t &c, const clause_t &cf, const literal_t &not_l);
static void prepare(void);
static bool write_formula(const char *path);
static bool convert_proof(const char *path_out, const char *path_in);
static bool write_parameter(std::ofstream &ofs , uint32_t val);
static bool write_step(std::ofstream &ofs, const step_t &s);
static bool write_delete(std::ofstream &ofs, const delete_t &dp);
static bool write_extend(std::ofstream &ofs, const extend_t &ep);
static bool write_literals(std::ofstream &ofs, const clause_t &c);
static bool write_indices(std::ofstream &ofs, const indices_t &is);
static bool write_rats(std::ofstream &ofs, const rats_t &rats);

// --- API ---------------------------------------------------------------------

int main(int argc, char *argv[])
{
    if (argc < 3 || argc > 5) {
        std::cerr << "usage: rewrite formula proof [proof' [formula']]" <<
                std::endl;
        return 1;
    }

    if (!read_formula(argv[1]) || !check_proof(argv[2])) {
        return 1;
    }

    if (argc == 3) {
        return 0;
    }

    prepare();

    if (!read_formula(argv[1])) {
        return 1;
    }

    if (argc == 5 && !write_formula(argv[4])) {
        return 1;
    }

    if (!convert_proof(argv[3], argv[2])) {
        return 1;
    }

    return 0;
}

// --- Helpers -----------------------------------------------------------------

#if DEBUG > 0
static void show_binary(uint32_t val, uint32_t n_bits)
{
    uint32_t mask = 1u << (n_bits - 1);

    for (uint32_t i = 0; i < n_bits; ++i) {
        std::cout << ((val & mask) == 0 ? "0" : "1");
        mask >>= 1;
    }
}

static void show_clause(const clause_t &c)
{
    for (auto it = c.cbegin(); it != c.cend(); ++it) {
        std::cout << (it->first == POSITIVE ? "pos " : "neg ");
        show_binary(it->second, g_bits_v);

        if (it + 1 != c.cend()) {
            std::cout << " : ";
        }
    }

    std::cout << std::endl;
}

static void show_formula(void)
{
    for (auto it = g_f.cbegin(); it != g_f.cend(); ++it) {
        index_t i = it->first;
        clause_t c = it->second;

        show_binary(i, g_bits_c);
        std::cout << " | ";
        show_clause(c);
    }
}
#endif

static bool read_formula(const char *path)
{
    std::ifstream ifs(path, std::ios::in);

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
    uint32_t dummy;

    if (!(ifs >> token) || token != "p" ||
            !(ifs >> token) || token != "cnf" ||
            !(ifs >> dummy) || !(ifs >> dummy)) {
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
    literal_t l = val < 0 ?
        std::make_pair(NEGATIVE, (variable_t)-val) :
        std::make_pair(POSITIVE, (variable_t)val);

    if (l.second > g_n_vars) {
        g_n_vars = l.second;
    }

    --l.second;
    return l;
}

static literal_t flip_lit(const literal_t &l)
{
    return l.first == POSITIVE ?
        std::make_pair(NEGATIVE, l.second) :
        std::make_pair(POSITIVE, l.second);
}

static bool check_proof(const char *path)
{
    std::ifstream ifs(path, std::ios::in);

    if (!ifs.is_open()) {
        std::cerr << "failed to open proof file " << path << std::endl;
        return false;
    }

    while (true) {
        ++g_n_steps;
        step_t s;

        if (!read_step(s, ifs) || !remap_step(s) || !run_step(s)) {
            return false;
        }

        if (s.type == EXTEND && s.extend.clause.empty()) {
            break;
        }
    }

    return true;
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

static bool remap_step(step_t &s)
{
    bool ok = s.type == DELETE ?
            remap_delete(s.delete_) : remap_extend(s.extend);

    if (!ok) {
        std::cerr << "failed to remap step " << g_n_steps << std::endl;
        return false;
    }

    return true;
}

static bool remap_delete(delete_t &dp)
{
    for (auto it = dp.indices.begin(); it != dp.indices.end(); ++it) {
        index_t i0 = *it;

        if (!map_index(*it)) {
            return false;
        }

        put_index(i0, *it);
    }

    return true;
}

static bool remap_extend(extend_t &ep)
{
    ep.index = get_index(ep.index);

    for (auto it = ep.rups.begin(); it != ep.rups.end(); ++it) {
        if (!map_index(*it)) {
            return false;
        }
    }

    for (auto it1 = ep.rats.begin(); it1 != ep.rats.end(); ++it1) {
        if (!map_index(it1->first)) {
            return false;
        }

        rups_t &rups = it1->second;

        for (auto it2 = rups.begin(); it2 != rups.end(); ++it2) {
            if (!map_index(*it2)) {
                return false;
            }
        }
    }

    std::sort(ep.rats.begin(), ep.rats.end()); // indices must remain in order
    return true;
}

static index_t get_index(index_t i0)
{
    index_t i;

    if (!g_recycler.empty()) {
        i = g_recycler.top();
        g_recycler.pop();
    }
    else {
        i = g_n_clauses++;
    }

    g_index_map.insert(std::make_pair(i0, i));
    return i;
}

static void put_index(index_t i0, index_t i)
{
    size_t n = g_index_map.erase(i0);
    assert (n == 1);
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

static bool run_step(const step_t &s)
{
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

    if (check_rat(c, ep.rats)) {
        g_f.insert(std::make_pair(ep.index, ep.clause));
        return true;
    }

    return false;
}

static result_t check_rup(clause_t &c, const rups_t &rups)
{
    for (auto it1 = rups.cbegin(); it1 != rups.cend(); ++it1) {
        const auto it2 = g_f.find(*it1);

        if (it2 == g_f.end()) {
            std::cerr << "invalid RUP index " << *it1 << std::endl;
            return FAIL;
        }

        const auto &diff = minus(it2->second, c);

        if (diff.first == 0) {
            return DONE;
        }

        if (diff.first > 1) {
            std::cerr << "non-unit clause for RUP index " << *it1 << std::endl;
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

static bool check_rat(clause_t &c, const rats_t &rats)
{
    if (c.empty()) {
        std::cerr << "RAT check with empty clause" << std::endl;
        return false;
    }

    literal_t l = c.front();
    literal_t not_l = flip_lit(l);
    uint32_t i_rat = 0;

    for (auto it = g_f.cbegin(); it != g_f.cend(); ++it) {
        index_t i = it->first;
        const clause_t &cf = it->second;

        if (!needs_check(cf, not_l)) {
            continue;
        }

        if (!validate_rats(rats, i_rat, i)) {
            std::cerr << "invalid RAT hints at index " << i << std::endl;
            return false;
        }

        if (!check_rat_rup(cf, c, l, not_l, rats[i_rat])) {
            std::cerr << "RAT clause check failed at index " << i << std::endl;
            return false;
        }

        ++i_rat;
    }

    return true;
}

static bool needs_check(const clause_t &cf, const literal_t &not_l)
{
    return std::find(cf.cbegin(), cf.cend(), not_l) != cf.cend();
}

static bool validate_rats(const rats_t &rats, uint32_t i_rat, index_t i)
{
    return i_rat < rats.size() && rats[i_rat].first == i;
}

static bool check_rat_rup(const clause_t &cf, const clause_t &c,
        const literal_t &l, const literal_t &not_l, const rat_t &rat)
{
    const rups_t &rups = rat.second;
    return rups.empty() ?
            check_clause_1(cf, c, l) : check_clause_2(cf, c, l, not_l, rups);
}

static bool check_clause_1(const clause_t &cf, const clause_t &c,
        const literal_t &l)
{
    // it's ok for |c| and |cf| to contain |not_l| and |l|, respectively, as
    // it makes both clauses tautologies:
    //   - |l| is |c|'s first literal by definition
    //   - |not_l| is in |cf| as we made it past needs_check() to get here
    for (auto it = c.cbegin(); it != c.cend(); ++it) {
        if (*it != l &&
                std::find(cf.cbegin(), cf.cend(), flip_lit(*it)) != cf.cend()) {
            return true;
        }
    }

    return false;
}

static bool check_clause_2(const clause_t &cf, const clause_t &c,
        const literal_t &l, const literal_t &not_l, const rups_t &rups)
{
    // make sure that dropping empty hints in write_rats() doesn't confuse
    // the Agda checker, which always runs check #1 and proceeds to check #2,
    // if that failed
    if (check_clause_1(cf, c, l)) {
        std::cerr << "non-empty hints need check #1 to fail" << std::endl;
        return false;
    }

    clause_t &&cr = resolvent(c, cf, not_l);
    return check_rup(cr, rups) == DONE;
}

static clause_t resolvent(const clause_t &c, const clause_t &cf,
        const literal_t &not_l)
{
    clause_t cr = c;

    for (auto it = cf.cbegin(); it != cf.cend(); ++it) {
        if (*it != not_l) {
            cr.push_back(*it);
        }
    }

    return cr;
}

static void prepare(void)
{
    --g_n_vars;
    --g_n_clauses;

    while (g_n_vars != 0) {
        ++g_bits_v;
        g_n_vars >>= 1;
    }

    while (g_n_clauses != 0) {
        ++g_bits_c;
        g_n_clauses >>= 1;
    }

    g_f.clear();
    g_index_map.clear();

    while (!g_recycler.empty()) {
        g_recycler.pop();
    }

    g_n_steps = 0;
}

static bool write_formula(const char *path)
{
    std::ofstream ofs(path, std::ios::out | std::ios::binary | std::ios::trunc);

    if (!ofs.is_open()) {
        std::cerr << "failed to create formula file " << path << std::endl;
        return false;
    }

    for (auto it1 = g_f.cbegin(); it1 != g_f.cend(); ++it1) {
        ofs << 'C';
        write_literals(ofs, it1->second);
        ofs << '\n';
    }

    return ofs.good();
}

static bool convert_proof(const char *path_out, const char *path_in)
{
    std::ifstream ifs(path_in, std::ios::in);

    if (!ifs.is_open()) {
        std::cerr << "failed to open proof file " << path_in << std::endl;
        return false;
    }

    std::ofstream ofs(path_out,
            std::ios::out | std::ios::binary | std::ios::trunc);

    if (!ofs.is_open()) {
        std::cerr << "failed to create proof file " << path_out << std::endl;
        return false;
    }

    if (!write_parameter(ofs, g_bits_v) || !write_parameter(ofs, g_bits_c)) {
        return false;
    }

    while (true) {
        ++g_n_steps;
        step_t s;

        if (!read_step(s, ifs) || !remap_step(s) || !write_step(ofs, s)) {
            return false;
        }

#if DEBUG > 0
        std::cout << g_n_steps << std::endl;
        show_formula();
#endif

        if (s.type == EXTEND && s.extend.clause.empty()) {
            break;
        }
    }

    return ofs.good();
}

static bool write_parameter(std::ofstream &ofs, uint32_t val)
{
    ofs << 'P';

    while (val-- > 0) {
        ofs << '+';
    }

    ofs << '.';
    ofs << '\n';

    return ofs.good();
}

static bool write_step(std::ofstream &ofs, const step_t &s)
{
    bool ok = s.type == DELETE ?
            write_delete(ofs, s.delete_) : write_extend(ofs, s.extend);

    if (!ok) {
        std::cerr << "step " << g_n_steps << " failed" << std::endl;
        return false;
    }

    return true;
}

static bool write_delete(std::ofstream &ofs, const delete_t &dp)
{
    ofs << 'D';

    if (!write_indices(ofs, dp.indices)) {
        return false;
    }

    ofs << '\n';
    return ofs.good();
}

static bool write_extend(std::ofstream &ofs, const extend_t &ep)
{
    ofs << 'E';

    if (!write_literals(ofs, ep.clause) ||
            !write_indices(ofs, ep.rups) ||
            !write_rats(ofs, ep.rats)) {
        return false;
    }

    ofs << '\n';
    return ofs.good();
}

static bool write_literals(std::ofstream &ofs, const literals_t &ls)
{
    for (auto it = ls.cbegin(); it != ls.cend(); ++it) {
        const literal_t &l = *it;
        uint32_t mask = 1u << (g_bits_v - 1);

        ofs << 'L' << (l.first == POSITIVE ? '+' : '-');

        for (uint32_t i = 0; i < g_bits_v; ++i) {
            ofs << ((l.second & mask) == 0 ? '0' : '1');
            mask >>= 1;
        }
    }

    ofs << '.';
    return ofs.good();
}

static bool write_indices(std::ofstream &ofs, const indices_t &is)
{
    for (auto it = is.cbegin(); it != is.cend(); ++it) {
        const index_t &i = *it;
        uint32_t mask = 1u << (g_bits_c - 1);

        ofs << 'I';

        for (uint32_t k = 0; k < g_bits_c; ++k) {
            ofs << ((i & mask) == 0 ? '0' : '1');
            mask >>= 1;
        }
    }

    ofs << '.';
    return ofs.good();
}

static bool write_rats(std::ofstream &ofs, const rats_t &rats)
{
    for (uint32_t i = 0; i < rats.size(); ++i) {
        const rat_t &rat = rats[i];
        const rups_t &rups = rat.second;

        if (!rups.empty()) {
            ofs << 'H';

            if (!write_indices(ofs, rups)) {
                return false;
            }
        }
    }

    ofs << '.';
    return ofs.good();
}
