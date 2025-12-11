#include <bits/stdc++.h>

using namespace std;

typedef long long ll;
typedef long double ld;
typedef double db;
typedef string str;

typedef pair<int,int> pi;
typedef pair<ll,ll> pl;
typedef pair<ld,ld> pld;

typedef set<int> si;
typedef set<ll> sl;
typedef set<ld> sld;
typedef set<str> ss;
typedef set<pi> spi;
typedef set<pl> spl;
typedef set<pld> spld;

typedef vector<int> vi;
typedef vector<ll> vl;
typedef vector<ld> vld;
typedef vector<str> vs;
typedef vector<pi> vpi;
typedef vector<pl> vpl;
typedef vector<si> vsi;
typedef vector<sl> vsl;
typedef vector<pld> vpld;

#define mp make_pair
#define f first
#define s second
#define sz(x) (int)(x).size()
#define all(x) begin(x), end(x)
#define rall(x) (x).rbegin(), (x).rend()
#define rsz resize
#define ins insert
#define ft front()
#define bk back()
#define pf push_front
#define pb push_back
#define eb emplace_back
#define lb lower_bound
#define ub upper_bound

#define forr(i,a,b) for (int i = (int)(a); i < (int)(b); i++)
#define ford(i,a,b) for (int i = (int)(a)-1; i >= (int)(b); i--)
#define trav(a,x) for (auto& a: x)

template<class T> bool ckmin(T& a, const T& b) { return b < a ? a = b, 1 : 0; }
template<class T> bool ckmax(T& a, const T& b) { return a < b ? a = b, 1 : 0; }
int pct(int x) { return __builtin_popcount(x); }
int bits(int x) { return 31-__builtin_clz(x); }
int fstTrue(function<bool(int)> f, int lo, int hi) {
    hi ++; assert(lo <= hi);
    while (lo < hi) {
        int mid = (lo+hi)/2;
        f(mid) ? hi = mid : lo = mid+1;
    }
    return lo;
}

const ll MOD = 1e9+7;
const int dx[8] = {1, 0, -1, 0, 1, 1, -1, -1}, dy[8] = {0, 1, 0, -1, -1, 1, -1, 1};
int gcd(int a,int b){return b?gcd(b,a%b):a;}
ll binpow(ll a,ll b){ll res=1;while(b){if(b&1)res=(res*a)%MOD;a=(a*a)%MOD;b>>=1;}return res;}
ll modInv(ll a){return binpow(a, MOD-2);}
bool sortcol(const vi& v1, const vi& v2) {return v1[1] < v2[1];}
bool sortpair(const pi& p1, const pi& p2) {return p1.f < p2.f;}

mt19937 rng((uint32_t)chrono::steady_clock::now().time_since_epoch().count());

inline uint32_t rng_next() { return (uint32_t)rng(); }
inline double rng_uniform() { return (double)rng_next() / (double)numeric_limits<uint32_t>::max(); }

template<class It>
inline void rng_shuffle(It b, It e) { shuffle(b, e, rng); }

inline int rng_randint(int a, int b) {
    uniform_int_distribution<int> dist(a, b);
    return dist(rng);
}

static const int RANKS[7] = {8,9,10,11,12,13,14};  // 8-A
struct Card { int r; int s; };  // rank and suit

vector<Card> make_deck() {
    vector<Card> d; d.reserve(28);
    for(int s=0; s<4; ++s)
        for(int k=0; k<7; ++k)
            d.push_back({RANKS[k], s});
    return d;
}

struct HandScore {
    int chips;
    array<int,5> kickers;
};

enum HandClass { HIGH_PAIR=0, TWO_PAIR=1, TRIPS=2, STRAIGHT=3, FULL_HOUSE=4, FOUR_KIND=5, FLUSH=6, STRAIGHT_FLUSH=7 };
const char* HAND_CLASS_NAMES[8] = {"High/Pair", "Two Pair", "Three of a Kind", "Straight", "Full House", "Four of a Kind", "Flush", "Straight Flush"};

// Evaluate poker hand and return chip value
HandScore eval_hand(const vector<Card>& cards) {
    array<int,15> rc{}; rc.fill(0);
    array<int,4> sc{};  sc.fill(0);
    for(auto &c : cards) { rc[c.r]++; sc[c.s]++; }

    auto is_straight_from = [&](int top) -> bool {
        for(int i=0; i<5; i++) if(top-i < 0 || rc[top-i]==0) return false;
        return true;
    };

    bool has_flush = false; int flushSuit = -1;
    for(int s=0; s<4; ++s) if(sc[s] >= 5) { has_flush = true; flushSuit = s; break; }

    int straight_top = 0;
    for(int top=14; top>=8; --top) {
        if(is_straight_from(top)) { straight_top = top; break; }
    }

    int sf_top = 0;
    if(has_flush) {
        array<int,15> rcF{}; rcF.fill(0);
        for(auto &c : cards) if(c.s == flushSuit) rcF[c.r]++;
        for(int top=14; top>=8; --top) {
            bool ok = true;
            for(int i=0; i<5; i++) if(rcF[top-i]==0) { ok=false; break; }
            if(ok) { sf_top = top; break; }
        }
    }

    int four=0, three=0;
    vector<int> pairs;
    for(int r=14; r>=8; --r) {
        if(rc[r]==4) four = r;
        else if(rc[r]==3) three = max(three, r);
        else if(rc[r]==2) pairs.push_back(r);
    }

    if(sf_top) return {5000, {sf_top,0,0,0,0}};
    if(has_flush) {
        vector<int> fr;
        for(auto &c : cards) if(c.s == flushSuit) fr.push_back(c.r);
        sort(fr.begin(), fr.end(), greater<int>());
        array<int,5> k{0,0,0,0,0};
        for(int i=0; i<5 && i<(int)fr.size(); ++i) k[i] = fr[i];
        return {1000, k};
    }
    if(four) {
        int kicker=0;
        for(int r=14; r>=8; --r) if(r!=four && rc[r]>0) { kicker=r; break; }
        return {500, {four, kicker, 0, 0, 0}};
    }
    if(three && pairs.size()) {
        int pair = pairs[0];
        return {75, {three, pair, 0, 0, 0}};
    }
    if(straight_top) return {30, {straight_top, 0, 0, 0, 0}};
    if(three) {
        int k1=0, k2=0;
        for(int r=14; r>=8; --r) if(r!=three && rc[r]>0) {
            if(!k1) k1=r; else { k2=r; break; }
        }
        return {10, {three, k1, k2, 0, 0}};
    }
    if(pairs.size() >= 2) {
        int p1=pairs[0], p2=pairs[1];
        int k=0;
        for(int r=14; r>=8; --r) if(r!=p1 && r!=p2 && rc[r]>0) { k=r; break; }
        return {5, {p1, p2, k, 0, 0}};
    }
    if(pairs.size() == 1) {
        int p = pairs[0];
        int k1=0, k2=0, k3=0;
        for(int r=14; r>=8; --r) if(r!=p && rc[r]>0) {
            if(!k1) k1=r; else if(!k2) k2=r; else { k3=r; break; }
        }
        return {0, {p, k1, k2, k3, 0}};
    }
    vector<int> all_cards;
    for(int r=14; r>=8; --r) for(int c=0; c<rc[r]; ++c) all_cards.push_back(r);
    sort(all_cards.begin(), all_cards.end(), greater<int>());
    array<int,5> k{0,0,0,0,0};
    for(int i=0; i<5 && i<(int)all_cards.size(); ++i) k[i] = all_cards[i];
    return {0, k};
}

int hand_class_from_chips(int chips) {
    if(chips >= 5000) return STRAIGHT_FLUSH;
    if(chips >= 1000) return FLUSH;
    if(chips >= 500)  return FOUR_KIND;
    if(chips >= 75)   return FULL_HOUSE;
    if(chips >= 30)   return STRAIGHT;
    if(chips >= 10)   return TRIPS;
    if(chips >= 5)    return TWO_PAIR;
    return HIGH_PAIR;
}

int chips_only(const vector<Card>& v) { return eval_hand(v).chips; }

struct GameParams {
    int budget = 50;
    int auctions = 12;
};

static const int BID_BINS_RAW[12] = {0,1,2,3,5,8,12,18,25,35,50,999999};
static const int NUM_BINS = 12;

vector<int> legal_bids(int dollars) {
    vector<int> acts;
    acts.reserve(NUM_BINS);
    for(int i=0; i<NUM_BINS; i++) {
        int b = BID_BINS_RAW[i];
        if(b == 999999) b = dollars;
        if(b <= dollars) acts.push_back(b);
    }
    if(!acts.empty()) {
        sort(all(acts));
        acts.erase(unique(all(acts)), acts.end());
    }
    return acts;
}

struct State {
    int idx;
    int dollars[2];
    vector<Card> hand[2];
    vector<vector<Card>> piles;
};

vector<vector<Card>> build_piles(int auctions) {
    vector<Card> d = make_deck();
    rng_shuffle(d.begin(), d.end());
    vector<vector<Card>> piles;
    piles.reserve(auctions);
    int ptr = 0, N = d.size();
    for(int i=0; i<auctions; i++) {
        int sz = 1 + (rng_next() % 4);
        if(ptr + sz > N) sz = N - ptr;
        if(sz <= 0) break;
        vector<Card> p;
        p.reserve(sz);
        for(int k=0; k<sz; k++) p.push_back(d[ptr++]);
        piles.push_back(move(p));
        if(ptr >= N) break;
    }
    return piles;
}

// CFR node storing regrets and strategy
struct Node {
    vector<double> regret;
    vector<double> strategy;
    vector<double> strategy_sum;
    int action_count;

    Node() : action_count(0) {}
    explicit Node(int A) : regret(A, 0.0), strategy(A, 1.0/A), strategy_sum(A, 0.0), action_count(A) {}

    void reset(int A) {
        regret.assign(A, 0.0);
        strategy.assign(A, 1.0/A);
        strategy_sum.assign(A, 0.0);
        action_count = A;
    }

    // CFR+ regret matching (clips negative regrets)
    void compute_strategy_cfr_plus() {
        double sum_pos = 0.0;
        for(int a=0; a<action_count; ++a) {
            if(regret[a] < 0) regret[a] = 0.0;
            sum_pos += regret[a];
        }
        if(sum_pos <= 1e-12) {
            double u = 1.0 / action_count;
            for(int a=0; a<action_count; ++a) strategy[a] = u;
        } else {
            for(int a=0; a<action_count; ++a) strategy[a] = regret[a] / sum_pos;
        }
    }

    // Vanilla CFR regret matching (allows negative regrets)
    void compute_strategy_vanilla() {
        double sum_pos = 0.0;
        for(int a=0; a<action_count; ++a) {
            sum_pos += max(0.0, regret[a]);
        }
        if(sum_pos <= 1e-12) {
            double u = 1.0 / action_count;
            for(int a=0; a<action_count; ++a) strategy[a] = u;
        } else {
            for(int a=0; a<action_count; ++a) strategy[a] = max(0.0, regret[a]) / sum_pos;
        }
    }

    vector<double> get_average_strategy() const {
        vector<double> avg(action_count);
        double total = 0.0;
        for(int a=0; a<action_count; ++a) total += strategy_sum[a];
        if(total <= 1e-12) {
            for(int a=0; a<action_count; ++a) avg[a] = 1.0 / action_count;
        } else {
            for(int a=0; a<action_count; ++a) avg[a] = strategy_sum[a] / total;
        }
        return avg;
    }
};

// MCCFR solver with CFR+ regrets and linear averaging
class MCCFRSolver {
public:
    unordered_map<string, Node> nodes;
    GameParams gp;
    int iteration;

    MCCFRSolver(GameParams params) : gp(params), iteration(0) {}

    string infoset_key(const State& st, int player, const vector<Card>& curHand, const vector<Card>& pile) {
        int dollars = st.dollars[player];
        int idx = st.idx;

        auto bucketize = [](int x) -> int {
            if(x >= 5000) return 7;
            if(x >= 1000) return 6;
            if(x >= 500)  return 5;
            if(x >= 75)   return 4;
            if(x >= 30)   return 3;
            if(x >= 10)   return 2;
            if(x >= 5)    return 1;
            return 0;
        };

        int cur_b = bucketize(chips_only(curHand));
        vector<Card> tmp = curHand;
        tmp.insert(tmp.end(), pile.begin(), pile.end());
        int win_b = bucketize(chips_only(tmp));
        int ps = (int)min<size_t>(pile.size(), 4);

        string k;
        k.reserve(24);
        k += to_string(idx);
        k.push_back('|');
        k += to_string(dollars);
        k.push_back('|');
        k += to_string(cur_b);
        k.push_back('|');
        k += to_string(win_b);
        k.push_back('|');
        k += to_string(ps);
        return k;
    }

    Node& get_node(const string& key, int A) {
        auto it = nodes.find(key);
        if(it == nodes.end()) {
            auto pr = nodes.try_emplace(key, Node(A));
            return pr.first->second;
        } else {
            if(it->second.action_count != A) it->second.reset(A);
            return it->second;
        }
    }

    int sample_action(const vector<double>& probs) {
        double r = rng_uniform();
        double acc = 0.0;
        for(int i=0; i<(int)probs.size(); ++i) {
            acc += probs[i];
            if(r <= acc) return i;
        }
        return (int)probs.size() - 1;
    }

    double self_play_traverse(State& st, double pi0, double pi1, double pi_sample) {
        if(st.idx >= (int)st.piles.size()) {
            int chips0 = eval_hand(st.hand[0]).chips;
            int chips1 = eval_hand(st.hand[1]).chips;
            return (double)(chips0 - chips1) / pi_sample;
        }

        const vector<Card>& pile = st.piles[st.idx];
        vector<int> acts0 = legal_bids(st.dollars[0]);
        vector<int> acts1 = legal_bids(st.dollars[1]);

        string k0 = infoset_key(st, 0, st.hand[0], pile);
        string k1 = infoset_key(st, 1, st.hand[1], pile);

        Node& n0 = get_node(k0, (int)acts0.size());
        Node& n1 = get_node(k1, (int)acts1.size());

        n0.compute_strategy_cfr_plus();
        n1.compute_strategy_cfr_plus();

        const double epsilon = 0.6;

        auto sample_with_exploration = [&](Node& n, const vi& acts) -> pair<int, double> {
            if(rng_uniform() < epsilon) {
                int idx = rng_randint(0, (int)acts.size() - 1);
                double p = epsilon / acts.size() + (1 - epsilon) * n.strategy[idx];
                return {idx, p};
            } else {
                int idx = sample_action(n.strategy);
                double p = epsilon / acts.size() + (1 - epsilon) * n.strategy[idx];
                return {idx, p};
            }
        };

        auto [a0_idx, p0] = sample_with_exploration(n0, acts0);
        auto [a1_idx, p1] = sample_with_exploration(n1, acts1);

        int bid0 = acts0[a0_idx];
        int bid1 = acts1[a1_idx];

        int winner = -1, price = 0;
        if(bid0 > bid1) { winner = 0; price = bid1; }
        else if(bid1 > bid0) { winner = 1; price = bid0; }
        else { winner = (rng_next() & 1) ? 0 : 1; price = bid0; }

        State next = st;
        if(winner == 0) {
            next.dollars[0] -= price;
            next.hand[0].insert(next.hand[0].end(), pile.begin(), pile.end());
        } else {
            next.dollars[1] -= price;
            next.hand[1].insert(next.hand[1].end(), pile.begin(), pile.end());
        }
        next.idx += 1;

        double new_pi0 = pi0 * n0.strategy[a0_idx];
        double new_pi1 = pi1 * n1.strategy[a1_idx];
        double new_pi_sample = pi_sample * p0 * p1;

        double util = self_play_traverse(next, new_pi0, new_pi1, new_pi_sample);

        double W = util * pi_sample;
        for(int i = 0; i < (int)acts0.size(); ++i) {
            if(i == a0_idx) {
                double regret = W * (1 - n0.strategy[i]) * pi1;
                n0.regret[i] += regret / (p0 * p1);
            } else {
                double regret = -W * n0.strategy[i] * pi1;
                n0.regret[i] += regret / p1;
            }
        }

        for(int i = 0; i < (int)acts1.size(); ++i) {
            if(i == a1_idx) {
                double regret = -W * (1 - n1.strategy[i]) * pi0;
                n1.regret[i] += regret / (p0 * p1);
            } else {
                double regret = W * n1.strategy[i] * pi0;
                n1.regret[i] += regret / p0;
            }
        }

        double weight = (double)iteration;
        for(int i = 0; i < (int)n0.strategy.size(); ++i) {
            n0.strategy_sum[i] += n0.strategy[i] * pi0 * weight;
        }
        for(int i = 0; i < (int)n1.strategy.size(); ++i) {
            n1.strategy_sum[i] += n1.strategy[i] * pi1 * weight;
        }

        return util;
    }

    void train_iteration() {
        iteration++;
        State st;
        st.idx = 0;
        st.dollars[0] = gp.budget;
        st.dollars[1] = gp.budget;
        st.piles = build_piles(gp.auctions);

        self_play_traverse(st, 1.0, 1.0, 1.0);
    }
};

// Vanilla CFR solver with uniform averaging
class CFRSolver {
public:
    unordered_map<string, Node> nodes;
    GameParams gp;
    int iteration;

    CFRSolver(GameParams params) : gp(params), iteration(0) {}

    string infoset_key(const State& st, int player, const vector<Card>& curHand, const vector<Card>& pile) {
        int dollars = st.dollars[player];
        int idx = st.idx;

        auto bucketize = [](int x) -> int {
            if(x >= 5000) return 7;
            if(x >= 1000) return 6;
            if(x >= 500)  return 5;
            if(x >= 75)   return 4;
            if(x >= 30)   return 3;
            if(x >= 10)   return 2;
            if(x >= 5)    return 1;
            return 0;
        };

        int cur_b = bucketize(chips_only(curHand));
        vector<Card> tmp = curHand;
        tmp.insert(tmp.end(), pile.begin(), pile.end());
        int win_b = bucketize(chips_only(tmp));
        int ps = (int)min<size_t>(pile.size(), 4);

        string k;
        k.reserve(24);
        k += to_string(idx);
        k.push_back('|');
        k += to_string(dollars);
        k.push_back('|');
        k += to_string(cur_b);
        k.push_back('|');
        k += to_string(win_b);
        k.push_back('|');
        k += to_string(ps);
        return k;
    }

    Node& get_node(const string& key, int A) {
        auto it = nodes.find(key);
        if(it == nodes.end()) {
            auto pr = nodes.try_emplace(key, Node(A));
            return pr.first->second;
        } else {
            if(it->second.action_count != A) it->second.reset(A);
            return it->second;
        }
    }

    int sample_action(const vector<double>& probs) {
        double r = rng_uniform();
        double acc = 0.0;
        for(int i=0; i<(int)probs.size(); ++i) {
            acc += probs[i];
            if(r <= acc) return i;
        }
        return (int)probs.size() - 1;
    }

    double self_play_traverse(State& st, double pi0, double pi1, double pi_sample) {
        if(st.idx >= (int)st.piles.size()) {
            int chips0 = eval_hand(st.hand[0]).chips;
            int chips1 = eval_hand(st.hand[1]).chips;
            return (double)(chips0 - chips1) / pi_sample;
        }

        const vector<Card>& pile = st.piles[st.idx];
        vector<int> acts0 = legal_bids(st.dollars[0]);
        vector<int> acts1 = legal_bids(st.dollars[1]);

        string k0 = infoset_key(st, 0, st.hand[0], pile);
        string k1 = infoset_key(st, 1, st.hand[1], pile);

        Node& n0 = get_node(k0, (int)acts0.size());
        Node& n1 = get_node(k1, (int)acts1.size());

        n0.compute_strategy_vanilla();
        n1.compute_strategy_vanilla();

        const double epsilon = 0.2;

        auto sample_with_exploration = [&](Node& n, const vi& acts) -> pair<int, double> {
            if(rng_uniform() < epsilon) {
                int idx = rng_randint(0, (int)acts.size() - 1);
                double p = epsilon / acts.size() + (1 - epsilon) * n.strategy[idx];
                return {idx, p};
            } else {
                int idx = sample_action(n.strategy);
                double p = epsilon / acts.size() + (1 - epsilon) * n.strategy[idx];
                return {idx, p};
            }
        };

        auto [a0_idx, p0] = sample_with_exploration(n0, acts0);
        auto [a1_idx, p1] = sample_with_exploration(n1, acts1);

        int bid0 = acts0[a0_idx];
        int bid1 = acts1[a1_idx];

        int winner = -1, price = 0;
        if(bid0 > bid1) { winner = 0; price = bid1; }
        else if(bid1 > bid0) { winner = 1; price = bid0; }
        else { winner = (rng_next() & 1) ? 0 : 1; price = bid0; }

        State next = st;
        if(winner == 0) {
            next.dollars[0] -= price;
            next.hand[0].insert(next.hand[0].end(), pile.begin(), pile.end());
        } else {
            next.dollars[1] -= price;
            next.hand[1].insert(next.hand[1].end(), pile.begin(), pile.end());
        }
        next.idx += 1;

        double new_pi0 = pi0 * n0.strategy[a0_idx];
        double new_pi1 = pi1 * n1.strategy[a1_idx];
        double new_pi_sample = pi_sample * p0 * p1;

        double util = self_play_traverse(next, new_pi0, new_pi1, new_pi_sample);

        double W = util * pi_sample;
        for(int i = 0; i < (int)acts0.size(); ++i) {
            if(i == a0_idx) {
                double regret = W * (1 - n0.strategy[i]) * pi1;
                n0.regret[i] += regret / (p0 * p1);
            } else {
                double regret = -W * n0.strategy[i] * pi1;
                n0.regret[i] += regret / p1;
            }
        }

        for(int i = 0; i < (int)acts1.size(); ++i) {
            if(i == a1_idx) {
                double regret = -W * (1 - n1.strategy[i]) * pi0;
                n1.regret[i] += regret / (p0 * p1);
            } else {
                double regret = W * n1.strategy[i] * pi0;
                n1.regret[i] += regret / p0;
            }
        }

        for(int i = 0; i < (int)n0.strategy.size(); ++i) {
            n0.strategy_sum[i] += n0.strategy[i] * pi0;
        }
        for(int i = 0; i < (int)n1.strategy.size(); ++i) {
            n1.strategy_sum[i] += n1.strategy[i] * pi1;
        }

        return util;
    }

    void train_iteration() {
        iteration++;
        State st;
        st.idx = 0;
        st.dollars[0] = gp.budget;
        st.dollars[1] = gp.budget;
        st.piles = build_piles(gp.auctions);

        self_play_traverse(st, 1.0, 1.0, 1.0);
    }
};

int sample_action_from_avg(const Node& n) {
    vector<double> avg = n.get_average_strategy();
    double r = rng_uniform();
    double acc = 0.0;
    for(int i = 0; i < (int)avg.size(); ++i) {
        acc += avg[i];
        if(r <= acc) return i;
    }
    return (int)avg.size() - 1;
}

struct EvalTrace {
    vector<int> prices;
    vector<int> winners;
    vector<int> bids_mccfr, bids_cfr;
    int payoff_diff = 0;
    int spent[2] = {0, 0};
    int class_mccfr = 0, class_cfr = 0;
    int chips_mccfr = 0, chips_cfr = 0;
};

double play_vs_random(MCCFRSolver& solver, GameParams& gp) {
    State st;
    st.idx = 0;
    st.dollars[0] = gp.budget;
    st.dollars[1] = gp.budget;
    st.piles = build_piles(gp.auctions);

    while(st.idx < (int)st.piles.size()) {
        const vector<Card>& pile = st.piles[st.idx];
        vector<int> a0 = legal_bids(st.dollars[0]);
        vector<int> a1 = legal_bids(st.dollars[1]);

        string k0 = solver.infoset_key(st, 0, st.hand[0], pile);

        auto get_avg = [&](const string& key, int A) -> vector<double> {
            auto it = solver.nodes.find(key);
            if(it == solver.nodes.end()) return vector<double>(A, 1.0/A);
            return it->second.get_average_strategy();
        };

        auto sample = [](const vector<double>& probs) -> int {
            double r = rng_uniform();
            double acc = 0.0;
            for(int i = 0; i < (int)probs.size(); ++i) {
                acc += probs[i];
                if(r <= acc) return i;
            }
            return (int)probs.size() - 1;
        };

        vector<double> p0 = get_avg(k0, (int)a0.size());
        int b0 = a0[sample(p0)];
        int b1 = a1[rng_randint(0, (int)a1.size()-1)];

        int winner = -1, price = 0;
        if(b0 > b1) { winner = 0; price = b1; }
        else if(b1 > b0) { winner = 1; price = b0; }
        else { winner = (rng_next() & 1) ? 0 : 1; price = b0; }

        if(winner == 0) {
            st.dollars[0] -= price;
            st.hand[0].insert(st.hand[0].end(), pile.begin(), pile.end());
        } else {
            st.dollars[1] -= price;
            st.hand[1].insert(st.hand[1].end(), pile.begin(), pile.end());
        }
        st.idx++;
    }

    int chips0 = eval_hand(st.hand[0]).chips;
    int chips1 = eval_hand(st.hand[1]).chips;
    return chips0 - chips1;
}

double play_vs_random_cfr(CFRSolver& solver, GameParams& gp) {
    State st;
    st.idx = 0;
    st.dollars[0] = gp.budget;
    st.dollars[1] = gp.budget;
    st.piles = build_piles(gp.auctions);

    while(st.idx < (int)st.piles.size()) {
        const vector<Card>& pile = st.piles[st.idx];
        vector<int> a0 = legal_bids(st.dollars[0]);
        vector<int> a1 = legal_bids(st.dollars[1]);

        string k0 = solver.infoset_key(st, 0, st.hand[0], pile);

        auto get_avg = [&](const string& key, int A) -> vector<double> {
            auto it = solver.nodes.find(key);
            if(it == solver.nodes.end()) return vector<double>(A, 1.0/A);
            return it->second.get_average_strategy();
        };

        auto sample = [](const vector<double>& probs) -> int {
            double r = rng_uniform();
            double acc = 0.0;
            for(int i = 0; i < (int)probs.size(); ++i) {
                acc += probs[i];
                if(r <= acc) return i;
            }
            return (int)probs.size() - 1;
        };

        vector<double> p0 = get_avg(k0, (int)a0.size());
        int b0 = a0[sample(p0)];
        int b1 = a1[rng_randint(0, (int)a1.size()-1)];

        int winner = -1, price = 0;
        if(b0 > b1) { winner = 0; price = b1; }
        else if(b1 > b0) { winner = 1; price = b0; }
        else { winner = (rng_next() & 1) ? 0 : 1; price = b0; }

        if(winner == 0) {
            st.dollars[0] -= price;
            st.hand[0].insert(st.hand[0].end(), pile.begin(), pile.end());
        } else {
            st.dollars[1] -= price;
            st.hand[1].insert(st.hand[1].end(), pile.begin(), pile.end());
        }
        st.idx++;
    }

    int chips0 = eval_hand(st.hand[0]).chips;
    int chips1 = eval_hand(st.hand[1]).chips;
    return chips0 - chips1;
}

double play_self_game(MCCFRSolver& solver, GameParams& gp) {
    State st;
    st.idx = 0;
    st.dollars[0] = gp.budget;
    st.dollars[1] = gp.budget;
    st.piles = build_piles(gp.auctions);

    while(st.idx < (int)st.piles.size()) {
        const vector<Card>& pile = st.piles[st.idx];
        vector<int> a0 = legal_bids(st.dollars[0]);
        vector<int> a1 = legal_bids(st.dollars[1]);

        string k0 = solver.infoset_key(st, 0, st.hand[0], pile);
        string k1 = solver.infoset_key(st, 1, st.hand[1], pile);

        auto get_avg = [&](const string& key, int A) -> vector<double> {
            auto it = solver.nodes.find(key);
            if(it == solver.nodes.end()) return vector<double>(A, 1.0/A);
            return it->second.get_average_strategy();
        };

        auto sample = [](const vector<double>& probs) -> int {
            double r = rng_uniform();
            double acc = 0.0;
            for(int i = 0; i < (int)probs.size(); ++i) {
                acc += probs[i];
                if(r <= acc) return i;
            }
            return (int)probs.size() - 1;
        };

        vector<double> p0 = get_avg(k0, (int)a0.size());
        vector<double> p1 = get_avg(k1, (int)a1.size());

        int b0 = a0[sample(p0)];
        int b1 = a1[sample(p1)];

        int winner = -1, price = 0;
        if(b0 > b1) { winner = 0; price = b1; }
        else if(b1 > b0) { winner = 1; price = b0; }
        else { winner = (rng_next() & 1) ? 0 : 1; price = b0; }

        if(winner == 0) {
            st.dollars[0] -= price;
            st.hand[0].insert(st.hand[0].end(), pile.begin(), pile.end());
        } else {
            st.dollars[1] -= price;
            st.hand[1].insert(st.hand[1].end(), pile.begin(), pile.end());
        }
        st.idx++;
    }

    int chips0 = eval_hand(st.hand[0]).chips;
    int chips1 = eval_hand(st.hand[1]).chips;
    return chips0 - chips1;
}

// Play evaluation game: MCCFR as P1, CFR as P2
EvalTrace play_eval_game(MCCFRSolver& mccfr, CFRSolver& cfr, GameParams& gp) {
    EvalTrace T;
    State st;
    st.idx = 0;
    st.dollars[0] = gp.budget;
    st.dollars[1] = gp.budget;
    st.piles = build_piles(gp.auctions);

    T.prices.reserve(st.piles.size());
    T.winners.reserve(st.piles.size());
    T.bids_mccfr.reserve(st.piles.size());
    T.bids_cfr.reserve(st.piles.size());

    while(st.idx < (int)st.piles.size()) {
        const vector<Card>& pile = st.piles[st.idx];
        vector<int> a0 = legal_bids(st.dollars[0]);
        vector<int> a1 = legal_bids(st.dollars[1]);

        string k0 = mccfr.infoset_key(st, 0, st.hand[0], pile);
        string k1 = cfr.infoset_key(st, 1, st.hand[1], pile);

        auto get_avg_mccfr = [&](const string& key, int A) -> vector<double> {
            auto it = mccfr.nodes.find(key);
            if(it == mccfr.nodes.end()) return vector<double>(A, 1.0/A);
            return it->second.get_average_strategy();
        };

        auto get_avg_cfr = [&](const string& key, int A) -> vector<double> {
            auto it = cfr.nodes.find(key);
            if(it == cfr.nodes.end()) return vector<double>(A, 1.0/A);
            return it->second.get_average_strategy();
        };

        vector<double> p0 = get_avg_mccfr(k0, (int)a0.size());
        vector<double> p1 = get_avg_cfr(k1, (int)a1.size());

        auto sample = [](const vector<double>& probs) -> int {
            double r = rng_uniform();
            double acc = 0.0;
            for(int i = 0; i < (int)probs.size(); ++i) {
                acc += probs[i];
                if(r <= acc) return i;
            }
            return (int)probs.size() - 1;
        };

        int b0 = a0[sample(p0)];
        int b1 = a1[sample(p1)];

        T.bids_mccfr.push_back(b0);
        T.bids_cfr.push_back(b1);

        int winner = -1, price = 0;
        if(b0 > b1) { winner = 0; price = b1; }
        else if(b1 > b0) { winner = 1; price = b0; }
        else { winner = (rng_next() & 1) ? 0 : 1; price = b0; }

        T.prices.push_back(price);
        T.winners.push_back(winner);

        if(winner == 0) {
            st.dollars[0] -= price;
            T.spent[0] += price;
            st.hand[0].insert(st.hand[0].end(), pile.begin(), pile.end());
        } else {
            st.dollars[1] -= price;
            T.spent[1] += price;
            st.hand[1].insert(st.hand[1].end(), pile.begin(), pile.end());
        }
        st.idx++;
    }

    T.chips_mccfr = eval_hand(st.hand[0]).chips;
    T.chips_cfr = eval_hand(st.hand[1]).chips;
    T.payoff_diff = T.chips_mccfr - T.chips_cfr;
    T.class_mccfr = hand_class_from_chips(T.chips_mccfr);
    T.class_cfr = hand_class_from_chips(T.chips_cfr);

    return T;
}

double evaluate_symmetric(MCCFRSolver& mccfr, CFRSolver& cfr, GameParams& gp, int games) {
    double total = 0;
    for(int g = 0; g < games; ++g) {
        EvalTrace t1 = play_eval_game(mccfr, cfr, gp);
        total += t1.payoff_diff;
    }
    return total / games;
}

struct Args {
    int time_ms = 5000;
    int seed = 42;
    int budget = 50;
    int auctions = 12;
    int eval_games = 200;
    string prefix = "auction";
};

void parse_args(int argc, char** argv, Args& args) {
    for(int i = 1; i < argc; i++) {
        string s(argv[i]);
        auto need = [&](int i) {
            if(i + 1 >= argc) {
                cerr << "Missing value for " << s << "\n";
                exit(1);
            }
        };

        if(s == "--time_ms") { need(i); args.time_ms = atoi(argv[++i]); }
        else if(s == "--seed") { need(i); args.seed = atoi(argv[++i]); }
        else if(s == "--budget") { need(i); args.budget = atoi(argv[++i]); }
        else if(s == "--auctions") { need(i); args.auctions = atoi(argv[++i]); }
        else if(s == "--eval") { need(i); args.eval_games = atoi(argv[++i]); }
        else if(s == "--prefix") { need(i); args.prefix = argv[++i]; }
        else if(s == "--help" || s == "-h") {
            cout << "Auction Poker Solver: MCCFR vs CFR (Time-Based)\n";
            cout << "Usage: ./auction_poker_solver [options]\n";
            cout << "Options:\n";
            cout << "  --time_ms N    Training time in ms for EACH method (default: 5000)\n";
            cout << "  --seed N       Random seed (default: 42)\n";
            cout << "  --budget N     Starting budget (default: 50)\n";
            cout << "  --auctions N   Number of auctions (default: 12)\n";
            cout << "  --eval N       Evaluation games (default: 200)\n";
            cout << "  --prefix S     Output file prefix (default: auction)\n";
            exit(0);
        }
        else { cerr << "Unknown arg: " << s << "\n"; exit(1); }
    }
}

int main(int argc, char** argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    Args args;
    parse_args(argc, argv, args);

    rng.seed((uint32_t)args.seed);

    cout << "Auction Poker: MCCFR vs CFR Comparison\n";
    cout << "Seed: " << args.seed << ", Time: " << args.time_ms << " ms, Budget: $" << args.budget << ", Auctions: " << args.auctions << "\n\n";

    GameParams gp;
    gp.budget = args.budget;
    gp.auctions = args.auctions;

    MCCFRSolver mccfr(gp);
    CFRSolver cfr_solver(gp);

    int mccfr_time = args.time_ms * 100;
    cout << "Training MCCFR for " << args.time_ms << " ms...\n";
    auto start_mccfr = chrono::high_resolution_clock::now();
    auto end_time_mccfr = start_mccfr + chrono::milliseconds(mccfr_time);

    int mccfr_iters = 0;
    while(chrono::high_resolution_clock::now() < end_time_mccfr) {
        mccfr.train_iteration();
        mccfr_iters++;
    }
    auto actual_mccfr = chrono::duration_cast<chrono::milliseconds>(
        chrono::high_resolution_clock::now() - start_mccfr).count();
    cout << "  MCCFR completed " << mccfr_iters << " iterations\n\n";

    cout << "Training CFR for " << args.time_ms << " ms...\n";
    auto start_cfr = chrono::high_resolution_clock::now();
    auto end_time_cfr = start_cfr + chrono::milliseconds(args.time_ms);

    int cfr_iters = 0;
    while(chrono::high_resolution_clock::now() < end_time_cfr) {
        cfr_solver.train_iteration();
        cfr_iters++;
    }
    auto actual_cfr = chrono::duration_cast<chrono::milliseconds>(
        chrono::high_resolution_clock::now() - start_cfr).count();
    cout << "  CFR completed " << cfr_iters << " iterations\n\n";

    cout << "Running " << args.eval_games << " evaluation games (MCCFR as P1, CFR as P2)...\n";

    int mccfr_wins = 0;
    long long sum = 0;
    vector<double> sum_price_by_idx(gp.auctions, 0.0);
    vector<int> count_by_idx(gp.auctions, 0);
    vector<int> mccfr_wins_by_idx(gp.auctions, 0);
    long long spent_sum[2] = {0, 0};
    array<long long, 8> cls_mccfr{}, cls_cfr{};
    cls_mccfr.fill(0);
    cls_cfr.fill(0);

    vector<int> payoff_diffs;
    vector<vector<int>> bids_by_auction_mccfr(gp.auctions);
    vector<vector<int>> bids_by_auction_cfr(gp.auctions);

    for(int g = 0; g < args.eval_games; ++g) {
        EvalTrace tr = play_eval_game(mccfr, cfr_solver, gp);
        sum += tr.payoff_diff;
        payoff_diffs.push_back(tr.payoff_diff);

        if(tr.payoff_diff > 0) mccfr_wins++;

        for(size_t i = 0; i < tr.prices.size() && i < (size_t)gp.auctions; ++i) {
            sum_price_by_idx[i] += tr.prices[i];
            count_by_idx[i] += 1;
            if(tr.winners[i] == 0) mccfr_wins_by_idx[i] += 1;
            bids_by_auction_mccfr[i].push_back(tr.bids_mccfr[i]);
            bids_by_auction_cfr[i].push_back(tr.bids_cfr[i]);
        }

        spent_sum[0] += tr.spent[0];
        spent_sum[1] += tr.spent[1];
        cls_mccfr[tr.class_mccfr]++;
        cls_cfr[tr.class_cfr]++;
    }

    double avg_payoff = sum / (double)args.eval_games;
    double win_rate = mccfr_wins / (double)args.eval_games;

    ofstream trainCSV(args.prefix + "_training.csv");
    trainCSV << "method,iterations,time_ms\n";
    trainCSV << "MCCFR," << mccfr_iters << "," << args.time_ms << "\n";
    trainCSV << "CFR," << cfr_iters << "," << args.time_ms << "\n";
    trainCSV.close();

    ofstream priceCSV(args.prefix + "_auction_stats.csv");
    priceCSV << "auction_index,avg_price,p1_winrate\n";
    for(int i = 0; i < gp.auctions; i++) {
        double denom = max(1, count_by_idx[i]);
        double avgp = sum_price_by_idx[i] / denom;
        double wri = mccfr_wins_by_idx[i] / denom;
        priceCSV << i << "," << avgp << "," << wri << "\n";
    }
    priceCSV.close();

    ofstream handCSV(args.prefix + "_hand_classes.csv");
    handCSV << "class,p1_count,p2_count\n";
    for(int c = 0; c < 8; c++) {
        handCSV << HAND_CLASS_NAMES[c] << "," << cls_mccfr[c] << "," << cls_cfr[c] << "\n";
    }
    handCSV.close();

    ofstream summaryCSV(args.prefix + "_summary.csv");
    summaryCSV << "metric,value\n";
    summaryCSV << "P1 average payoff (chips difference)," << avg_payoff << "\n";
    summaryCSV << "P1 win rate (chips better than opponent)," << win_rate << "\n";
    summaryCSV.close();

    ofstream payoffCSV(args.prefix + "_payoff_dist.csv");
    payoffCSV << "payoff_diff\n";
    for(int pd : payoff_diffs) {
        payoffCSV << pd << "\n";
    }
    payoffCSV.close();

    cout << "\nResults:\n";
    cout << "P1 avg payoff: " << fixed << setprecision(3) << avg_payoff << "\n";
    cout << "P1 win rate: " << fixed << setprecision(4) << win_rate << "\n\n";

    cout << "Hand classes (P1/P2):\n";
    for(int c = 0; c < 8; c++) {
        cout << HAND_CLASS_NAMES[c] << ": " << cls_mccfr[c] << "/" << cls_cfr[c] << "\n";
    }
    cout << "\n";

    cout << "Per-auction (idx, avg_price, p1_wr):\n";
    for(int i = 0; i < gp.auctions; i++) {
        double denom = max(1, count_by_idx[i]);
        double avgp = sum_price_by_idx[i] / denom;
        double wri = mccfr_wins_by_idx[i] / denom;
        cout << i << ": " << fixed << setprecision(2) << avgp << ", " << setprecision(3) << wri << "\n";
    }
    cout << "\n";

    cout << "Output files:\n";
    cout << "  " << args.prefix << "_training.csv\n";
    cout << "  " << args.prefix << "_auction_stats.csv\n";
    cout << "  " << args.prefix << "_hand_classes.csv\n";
    cout << "  " << args.prefix << "_summary.csv\n";
    cout << "  " << args.prefix << "_payoff_dist.csv\n";

    return 0;
}
