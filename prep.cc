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
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

// --- Types and constants -----------------------------------------------------

typedef uint32_t u32;
typedef int64_t i64;

typedef u32 variable_t;
typedef enum { POSITIVE, NEGATIVE } polarity_t;
typedef std::pair<polarity_t, variable_t> literal_t;

typedef u32 index_t;
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

typedef std::unordered_map<index_t, index_t> index_map_t;
template <class T> using min_heap_t =
        std::priority_queue<T, std::vector<T>, std::greater<T>>;
typedef min_heap_t<index_t> recycler_t;

class fail_ : public std::ostringstream {
public:
    [[noreturn]] ~fail_() {
        std::cerr << str();
        ::exit(1);
    }
};

#define fail fail_{}
#define DEBUG 0

// --- Macros and inline functions ---------------------------------------------

// --- Globals -----------------------------------------------------------------

static variable_t g_n_vars = 0;
static index_t g_n_clauses = 0;
static formula_t g_f;
static u32 g_n_steps = 0;

static index_map_t g_index_map;
static recycler_t g_recycler;

static u32 g_bits_v;
static u32 g_bits_c;

// --- Helper declarations -----------------------------------------------------

#if DEBUG > 0
static void show_binary(u32 val, u32 n_bits);
static void show_clause(const clause_t &c);
static void show_formula(void);
#endif

static literal_t make_lit(i64 val);
static literal_t flip_lit(const literal_t &l);

static void read_formula(const char *path);
static void read_header(std::ifstream &ifs);
static void read_body(std::ifstream &ifs);

static void check_proof(const char *path);
static void read_step(step_t &s, std::ifstream &ifs);
static void read_delete(step_t &s, std::ifstream &ifs);
static void read_extend(step_t &s, index_t i, i64 val, std::ifstream &ifs);

static void read_clause(clause_t &c, i64 &val, std::ifstream &ifs);
static void read_rup(rups_t &rups, i64 &val, std::ifstream &ifs);
static void read_rat(rats_t &rats, i64 &val, std::ifstream &ifs);

static void remap_step(step_t &s);
static void remap_delete(delete_t &dp);
static void remap_extend(extend_t &ep);

static index_t get_index(index_t i0);
static void put_index(index_t i0, index_t i);
static void map_index(index_t &i);

static void run_step(const step_t &s);
static void run_delete(const delete_t &dp);
static void run_extend(const extend_t &ep);

static bool run_rup(clause_t &c, const rups_t &rups);
static clause_t minus(const clause_t &c1, const clause_t &c2);

static void run_rat(clause_t &c, const rats_t &rats);
static bool needs_check(const clause_t &cf, const literal_t &not_l);
static void check_rat_rup(const clause_t &cf, const clause_t &c, const literal_t &l, const literal_t &not_l, const rats_t &rats, index_t i, u32 i_rat);
static void check_complement(const clause_t &cf, const clause_t &c, const literal_t &l);
static void check_resolvent(const clause_t &cf, const clause_t &c, const literal_t &not_l, const rups_t &rups);
static clause_t resolvent(const clause_t &c, const clause_t &cf, const literal_t &not_l);

static void prepare(void);
static void write_formula(const char *path);
static void convert_proof(const char *path_out, const char *path_in);
static void write_parameter(std::ofstream &ofs , u32 val);
static void write_step(std::ofstream &ofs, const step_t &s);
static void write_delete(std::ofstream &ofs, const delete_t &dp);
static void write_extend(std::ofstream &ofs, const extend_t &ep);
static void write_literals(std::ofstream &ofs, const clause_t &c);
static void write_indices(std::ofstream &ofs, const indices_t &is);
static void write_rats(std::ofstream &ofs, const rats_t &rats);

// --- API ---------------------------------------------------------------------

int main(int argc, char *argv[])
{
    if (argc < 3 || argc > 5) {
        fail << "usage: prep formula proof [proof' [formula']]" << std::endl;
    }

    read_formula(argv[1]);
    check_proof(argv[2]);

    if (argc == 3) {
        return 0;
    }

    prepare();
    read_formula(argv[1]);

    if (argc == 5) {
        write_formula(argv[4]);
    }

    convert_proof(argv[3], argv[2]);
    return 0;
}

// --- Helpers -----------------------------------------------------------------

#if DEBUG > 0
static void show_binary(u32 val, u32 n_bits)
{
    u32 mask = 1u << (n_bits - 1);

    for (u32 b = 0; b < n_bits; ++b) {
        std::cout << ((val & mask) == 0 ? "0" : "1");
        mask >>= 1;
    }
}

static void show_clause(const clause_t &c)
{
    bool first = true;

    for (const auto &lc : c) {
        if (first) {
            first = false;
        } else {
            std::cout << " : ";
        }

        std::cout << (lc.first == POSITIVE ? "pos " : "neg ");
        show_binary(lc.second, g_bits_v);
    }

    std::cout << std::endl;
}

static void show_formula(void)
{
    for (const auto &[i, cf] : g_f) {
        show_binary(i, g_bits_c);
        std::cout << " | ";
        show_clause(cf);
    }
}
#endif

static literal_t make_lit(i64 val)
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

static void read_formula(const char *path)
{
    std::ifstream ifs(path, std::ios::in);

    if (!ifs.is_open()) {
        fail << "failed to open formula file " << path << std::endl;
    }

    read_header(ifs);
    read_body(ifs);
}

static void read_header(std::ifstream &ifs)
{
    std::string token;
    u32 dummy;

    if (!(ifs >> token) || token != "p" || !(ifs >> token) || token != "cnf" ||
            !(ifs >> dummy) || !(ifs >> dummy)) {
        fail << "invalid header" << std::endl;
    }
}

static void read_body(std::ifstream &ifs)
{
    index_t i0 = 0;
    clause_t c;
    i64 val;

    while (ifs >> val) {
        if (val == 0) {
            index_t i = get_index(++i0);
            g_f.insert(std::make_pair(i, c));
            c.clear();
        } else {
            literal_t l = make_lit(val);
            c.push_back(l);
        }
    }

    if (!ifs.eof() || val != 0) {
        fail << "invalid body" << std::endl;
    }
}

static void check_proof(const char *path)
{
    std::ifstream ifs(path, std::ios::in);

    if (!ifs.is_open()) {
        fail << "failed to open proof file " << path << std::endl;
    }

    while (true) {
        step_t s;

        ++g_n_steps;
        read_step(s, ifs);
        remap_step(s);
        run_step(s);

        if (s.type == EXTEND && s.extend.clause.empty()) {
            break;
        }
    }
}

static void read_step(step_t &s, std::ifstream &ifs)
{
    index_t i;
    std::string str;

    if (!(ifs >> i) || !(ifs >> str)) {
        fail << "invalid step" << std::endl;
    }

    if (str == "d") {
        read_delete(s, ifs);
    } else {
        i64 val = strtoll(str.c_str(), NULL, 10);
        read_extend(s, i, val, ifs);
    }
}

static void read_delete(step_t &s, std::ifstream &ifs)
{
    s.type = DELETE;
    delete_t &dp = s.delete_;
    index_t i;

    while (ifs >> i) {
        if (i == 0) {
            return;
        }

        dp.indices.push_back(i);
    }

    fail << "invalid delete step" << std::endl;
}

static void read_extend(step_t &s, index_t i, i64 val, std::ifstream &ifs)
{
    s.type = EXTEND;
    extend_t &ep = s.extend;
    ep.index = i;

    read_clause(ep.clause, val, ifs);
    read_rup(ep.rups, val, ifs);

    if (val != 0) {
        read_rat(ep.rats, val, ifs);
    }
}

static void read_clause(clause_t &c, i64 &val, std::ifstream &ifs)
{
    while (val != 0) {
        literal_t l = make_lit(val);
        c.push_back(l);

        if (!(ifs >> val)) {
            fail << "invalid clause" << std::endl;
        }
    }
}

static void read_rup(rups_t &rups, i64 &val, std::ifstream &ifs)
{
    while (true) {
        if (!(ifs >> val)) {
            fail << "invalid RUP hints" << std::endl;
        }

        if (val <= 0) {
            return;
        }

        rups.push_back((index_t)val);
    }
}

static void read_rat(rats_t &rats, i64 &val, std::ifstream &ifs)
{
    index_t i = (index_t)-val;
    rups_t rups;

    while (true) {
        if (!(ifs >> val)) {
            fail << "invalid RAT hints" << std::endl;
        }

        if (val > 0) {
            rups.push_back((index_t)val);
        } else {
            rats.push_back(std::make_pair(i, rups));

            if (val == 0) {
                return;
            }

            i = (index_t)-val;
            rups.clear();
        }
    }
}

static void remap_step(step_t &s)
{
    if (s.type == DELETE) {
        remap_delete(s.delete_);
    } else {
        remap_extend(s.extend);
    }
}

static void remap_delete(delete_t &dp)
{
    for (auto &i : dp.indices) {
        index_t i0 = i;
        map_index(i);
        put_index(i0, i);
    }
}

static void remap_extend(extend_t &ep)
{
    ep.index = get_index(ep.index);

    for (auto &i : ep.rups) {
        map_index(i);
    }

    for (auto &[i, rups] : ep.rats) {
        map_index(i);

        for (auto &k : rups) {
            map_index(k);
        }
    }

    std::sort(ep.rats.begin(), ep.rats.end()); // indices must remain in order
}

static index_t get_index(index_t i0)
{
    index_t i;

    if (!g_recycler.empty()) {
        i = g_recycler.top();
        g_recycler.pop();
    } else {
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

static void map_index(index_t &i)
{
    const auto it = g_index_map.find(i);

    if (it == g_index_map.end()) {
        fail << "failed to map index " << i << " in step " << g_n_steps <<
                std::endl;
    }

    i = it->second;
}

static void run_step(const step_t &s)
{
    if (s.type == DELETE) {
        run_delete(s.delete_);
    } else {
        run_extend(s.extend);
    }
}

static void run_delete(const delete_t &dp)
{
    for (const auto &i : dp.indices) {
        if (g_f.erase(i) == 0) {
            fail << "invalid delete index " << i << " in step " << g_n_steps <<
                    std::endl;
        }
    }
}

static void run_extend(const extend_t &ep)
{
    clause_t c = ep.clause;

    if (!run_rup(c, ep.rups)) {
        run_rat(c, ep.rats);
    }

    g_f.insert(std::make_pair(ep.index, ep.clause));
}

static bool run_rup(clause_t &c, const rups_t &rups)
{
    for (const auto &i : rups) {
        const auto it = g_f.find(i);

        if (it == g_f.end()) {
            fail << "invalid RUP index " << i << " in step " << g_n_steps <<
                    std::endl;
        }

        const auto &diff = minus(it->second, c);

        if (diff.size() == 0) {
            return true;
        }

        if (diff.size() > 1) {
            fail << "non-unit clause for RUP index " << i << " in step " <<
                    g_n_steps << std::endl;
        }

        c.push_back(flip_lit(diff.front()));
    }

    return false;
}

static clause_t minus(const clause_t &c1, const clause_t &c2)
{
    clause_t diff;

    for (const auto &lc1 : c1) {
        if (std::find(c2.cbegin(), c2.cend(), lc1) == c2.cend()) {
            diff.push_back(lc1);
        }
    }

    return diff;
}

static void run_rat(clause_t &c, const rats_t &rats)
{
    if (c.empty()) {
        fail << "RAT check with empty clause in step " << g_n_steps <<
                std::endl;
    }

    literal_t l = c.front();
    literal_t not_l = flip_lit(l);
    u32 i_rat = 0;

    for (const auto &[i, cf] : g_f) {
        if (needs_check(cf, not_l)) {
            check_rat_rup(cf, c, l, not_l, rats, i, i_rat);
            ++i_rat;
        }
    }
}

static bool needs_check(const clause_t &cf, const literal_t &not_l)
{
    return std::find(cf.cbegin(), cf.cend(), not_l) != cf.cend();
}

static void check_rat_rup(const clause_t &cf, const clause_t &c,
        const literal_t &l, const literal_t &not_l, const rats_t &rats,
        index_t i, u32 i_rat)
{
    if (i_rat >= rats.size() || rats[i_rat].first != i) {
        fail << "invalid RAT hints in step " << g_n_steps << std::endl;
    }

    const rups_t &rups = rats[i_rat].second;

    if (rups.empty()) {
        check_complement(cf, c, l);
    } else {
        check_resolvent(cf, c, not_l, rups);
    }
}

static void check_complement(const clause_t &cf, const clause_t &c,
        const literal_t &l)
{
    for (const auto &lc : c) {
        if (lc != l &&
                std::find(cf.cbegin(), cf.cend(), flip_lit(lc)) != cf.cend()) {
            return;
        }
    }

    fail << "complement check failed in step " << g_n_steps << std::endl;
}

static void check_resolvent(const clause_t &cf, const clause_t &c,
        const literal_t &not_l, const rups_t &rups)
{
    clause_t &&cr = resolvent(c, cf, not_l);

    if (!run_rup(cr, rups)) {
        fail << "resolvent check failed in step " << g_n_steps << std::endl;
    }
}

static clause_t resolvent(const clause_t &c, const clause_t &cf,
        const literal_t &not_l)
{
    clause_t cr = c;

    for (const auto &lcf : cf) {
        if (lcf != not_l) {
            cr.push_back(lcf);
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

static void write_formula(const char *path)
{
    std::ofstream ofs(path, std::ios::out | std::ios::binary | std::ios::trunc);

    if (!ofs.is_open()) {
        fail << "failed to create formula file " << path << std::endl;
    }

    for (const auto &[i, cf] : g_f) {
        (void)i;
        ofs << 'C';
        write_literals(ofs, cf);
        ofs << '\n';
    }

    if (!ofs.good()) {
        fail << "failed to write formula" << std::endl;
    }
}

static void convert_proof(const char *path_out, const char *path_in)
{
    std::ifstream ifs(path_in, std::ios::in);

    if (!ifs.is_open()) {
        fail << "failed to open proof file " << path_in << std::endl;
    }

    std::ofstream ofs(path_out,
            std::ios::out | std::ios::binary | std::ios::trunc);

    if (!ofs.is_open()) {
        fail << "failed to create proof file " << path_out << std::endl;
    }

    write_parameter(ofs, g_bits_v);
    write_parameter(ofs, g_bits_c);

    while (true) {
        step_t s;

        ++g_n_steps;
        read_step(s, ifs);
        remap_step(s);
        write_step(ofs, s);

        if (s.type == EXTEND && s.extend.clause.empty()) {
            break;
        }
    }

    if (!ofs.good()) {
        fail << "failed to write proof" << std::endl;
    }
}

static void write_parameter(std::ofstream &ofs, u32 val)
{
    ofs << 'P';

    while (val-- > 0) {
        ofs << '+';
    }

    ofs << '.';
    ofs << '\n';
}

static void write_step(std::ofstream &ofs, const step_t &s)
{
    if (s.type == DELETE) {
        write_delete(ofs, s.delete_);
    } else {
        write_extend(ofs, s.extend);
    }
}

static void write_delete(std::ofstream &ofs, const delete_t &dp)
{
    ofs << 'D';
    write_indices(ofs, dp.indices);
    ofs << '\n';
}

static void write_extend(std::ofstream &ofs, const extend_t &ep)
{
    ofs << 'E';
    write_literals(ofs, ep.clause);
    write_indices(ofs, ep.rups);
    write_rats(ofs, ep.rats);
    ofs << '\n';
}

static void write_literals(std::ofstream &ofs, const literals_t &ls)
{
    for (const auto &l : ls) {
        u32 mask = 1u << (g_bits_v - 1);
        ofs << 'L' << (l.first == POSITIVE ? '+' : '-');

        for (u32 b = 0; b < g_bits_v; ++b) {
            ofs << ((l.second & mask) == 0 ? '0' : '1');
            mask >>= 1;
        }
    }

    ofs << '.';
}

static void write_indices(std::ofstream &ofs, const indices_t &is)
{
    for (const auto &i : is) {
        u32 mask = 1u << (g_bits_c - 1);
        ofs << 'I';

        for (u32 b = 0; b < g_bits_c; ++b) {
            ofs << ((i & mask) == 0 ? '0' : '1');
            mask >>= 1;
        }
    }

    ofs << '.';
}

static void write_rats(std::ofstream &ofs, const rats_t &rats)
{
    for (u32 i_rat = 0; i_rat < rats.size(); ++i_rat) {
        const auto &[i, rups] = rats[i_rat];
        (void)i;

        if (!rups.empty()) {
            ofs << 'H';
            write_indices(ofs, rups);
        }
    }

    ofs << '.';
}
