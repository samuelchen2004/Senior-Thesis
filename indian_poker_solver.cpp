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

inline ld rng_uniform() {
    return (ld)rng() / (ld)numeric_limits<uint32_t>::max();
}

inline int rng_int(int a, int b) {
    uniform_int_distribution<int> dist(a, b);
    return dist(rng);
}

const int NUM_RANKS = 13;
const int ACTIONS = 6;  // fold, call, raise3x, raise5x, raise10x, shove
const str ACTION_NAMES[6] = {"f", "c", "r3", "r5", "r10", "s"};

// Information set node for CFR
struct InfoSet {
    str key;
    vld regret_sum;
    vld strategy_sum;
    vld strategy;
    ld reach_pr_sum = 0;

    InfoSet() {}

    void init(const str& k) {
        key = k;
        regret_sum.assign(ACTIONS, 0);
        strategy_sum.assign(ACTIONS, 0);
        strategy.assign(ACTIONS, 1.0L / ACTIONS);
        reach_pr_sum = 0;
    }

    // Regret matching to compute current strategy
    void compute_strategy() {
        ld total = 0;
        forr(i, 0, ACTIONS) {
            strategy[i] = max(regret_sum[i], (ld)0);
            total += strategy[i];
        }
        if (total > 0) {
            forr(i, 0, ACTIONS) strategy[i] /= total;
        } else {
            forr(i, 0, ACTIONS) strategy[i] = 1.0L / ACTIONS;
        }
    }

    // Average strategy over all iterations (used for play)
    vld get_average_strategy() const {
        vld s(ACTIONS);
        ld total = 0;
        forr(i, 0, ACTIONS) total += strategy_sum[i];

        if (total <= 1e-12) {
            forr(i, 0, ACTIONS) s[i] = 1.0L / ACTIONS;
        } else {
            forr(i, 0, ACTIONS) {
                s[i] = strategy_sum[i] / total;
                if (s[i] < 0.001) s[i] = 0;
            }
            ld sum = 0;
            forr(i, 0, ACTIONS) sum += s[i];
            if (sum > 0) forr(i, 0, ACTIONS) s[i] /= sum;
        }
        return s;
    }

    int sample_action() const {
        vld avg = get_average_strategy();
        ld r = rng_uniform();
        ld acc = 0;
        forr(i, 0, ACTIONS) {
            acc += avg[i];
            if (r <= acc) return i;
        }
        return ACTIONS - 1;
    }

    int sample_from_current() const {
        ld r = rng_uniform();
        ld acc = 0;
        forr(i, 0, ACTIONS) {
            acc += strategy[i];
            if (r <= acc) return i;
        }
        return ACTIONS - 1;
    }
};

class CFRAgent {
public:
    map<str, InfoSet> nodes;
    str name;

    CFRAgent(const str& n) : name(n) {}

    InfoSet& get_or_create(const str& key) {
        if (nodes.find(key) == nodes.end()) {
            nodes[key].init(key);
        }
        return nodes[key];
    }
};

bool is_legal(int action, bool is_p1_turn, ld bet1, ld bet2, bool first_action) {
    if (action == 0) return true;
    if (action == 1) return !first_action;
    if (bet1 >= 100 || bet2 >= 100) return false;

    if (action == 2) {
        ld new_bet = is_p1_turn ? 3 * bet2 : 3 * bet1;
        return new_bet < 100;
    }
    if (action == 3) {
        ld new_bet = is_p1_turn ? 5 * bet2 : 5 * bet1;
        return new_bet < 100;
    }
    if (action == 4) {
        ld new_bet = is_p1_turn ? 10 * bet2 : 10 * bet1;
        return new_bet < 100;
    }
    if (action == 5) {
        return bet1 < 100 && bet2 < 100;
    }
    return false;
}

// Calculate payoff at terminal node (call or fold)
ld get_terminal_payoff(char end, int c1, int c2, bool is_p1_turn, ld bet1, ld bet2) {
    if (end == 'c') {
        if (c1 == c2) return 0;
        if (c1 > c2) return bet1;
        return -bet1;
    } else {
        if (is_p1_turn) {
            if (c1 == 12) return bet2 + (100 - bet2) / 2.0L;
            return bet2;
        } else {
            if (c2 == 12) return -(bet1 + (100 - bet1) / 2.0L);
            return -bet1;
        }
    }
}

void apply_action(int action, bool is_p1_turn, ld& bet1, ld& bet2) {
    if (action == 0) return;
    if (action == 1) {
        if (is_p1_turn) bet1 = bet2;
        else bet2 = bet1;
    } else if (action == 2) {
        if (is_p1_turn) bet1 = 3 * bet2;
        else bet2 = 3 * bet1;
    } else if (action == 3) {
        if (is_p1_turn) bet1 = 5 * bet2;
        else bet2 = 5 * bet1;
    } else if (action == 4) {
        if (is_p1_turn) bet1 = 10 * bet2;
        else bet2 = 10 * bet1;
    } else if (action == 5) {
        if (is_p1_turn) bet1 = 100;
        else bet2 = 100;
    }
}

// CFR tree traversal - full game tree exploration
ld cfr_traverse(CFRAgent& agent, str history, int c1, int c2,
                ld p1, ld p2, ld pc, bool is_p1_turn,
                ld bet1, ld bet2) {
    char last = history.empty() ? ' ' : history.back();
    if (last == 'c' || last == 'f') {
        return get_terminal_payoff(last, c1, c2, is_p1_turn, bet1, bet2);
    }

    int visible_card = is_p1_turn ? c2 : c1;
    str key = to_string(visible_card) + " " + history;

    InfoSet& info = agent.get_or_create(key);
    info.compute_strategy();
    vld& s = info.strategy;

    bool first_action = (history.length() <= 2);
    vld action_utils(ACTIONS, 0);
    si invalid;

    forr(a, 0, ACTIONS) {
        if (!is_legal(a, is_p1_turn, bet1, bet2, first_action)) {
            invalid.insert(a);
            continue;
        }

        str new_history = history + ACTION_NAMES[a];
        ld new_bet1 = bet1, new_bet2 = bet2;
        apply_action(a, is_p1_turn, new_bet1, new_bet2);

        if (is_p1_turn) {
            action_utils[a] = -cfr_traverse(agent, new_history, c1, c2,
                                            p1 * s[a], p2, pc, !is_p1_turn,
                                            new_bet1, new_bet2);
        } else {
            action_utils[a] = -cfr_traverse(agent, new_history, c1, c2,
                                            p1, p2 * s[a], pc, !is_p1_turn,
                                            new_bet1, new_bet2);
        }
    }

    ld util = 0;
    forr(a, 0, ACTIONS) {
        if (invalid.count(a)) continue;
        util += action_utils[a] * s[a];
    }

    vld regrets(ACTIONS, 0);
    forr(a, 0, ACTIONS) {
        if (invalid.count(a)) continue;
        regrets[a] = action_utils[a] - util;
    }

    ld opp_reach = is_p1_turn ? p2 : p1;
    forr(a, 0, ACTIONS) {
        info.regret_sum[a] += opp_reach * pc * regrets[a];
    }

    ld my_reach = is_p1_turn ? p1 : p2;
    forr(a, 0, ACTIONS) {
        info.strategy_sum[a] += my_reach * s[a];
    }

    return util;
}

ld cfr_iteration(CFRAgent& agent) {
    ld total_util = 0;
    forr(c1, 0, NUM_RANKS) {
        forr(c2, 0, NUM_RANKS) {
            ld pc = (c1 == c2) ? (12.0L / 2652.0L) : (16.0L / 2652.0L);
            total_util += cfr_traverse(agent, "rr", c1, c2, 1, 1, pc, true, 0.5, 1);
        }
    }
    return total_util / (NUM_RANKS * NUM_RANKS);
}

vi get_legal_actions(bool is_p1_turn, ld bet1, ld bet2, bool first_action) {
    vi legal;
    forr(a, 0, ACTIONS) {
        if (is_legal(a, is_p1_turn, bet1, bet2, first_action)) {
            legal.pb(a);
        }
    }
    return legal;
}

pair<int, ld> sample_action_with_prob(const vld& strategy, const vi& legal_actions) {
    vld probs;
    ld total = 0;
    for (int a : legal_actions) {
        probs.pb(strategy[a]);
        total += strategy[a];
    }
    if (total < 1e-12) {
        ld u = 1.0L / legal_actions.size();
        for (auto& p : probs) p = u;
        total = 1.0L;
    } else {
        for (auto& p : probs) p /= total;
    }

    ld r = rng_uniform();
    ld acc = 0;
    for (size_t i = 0; i < probs.size(); i++) {
        acc += probs[i];
        if (r <= acc) {
            return {legal_actions[i], probs[i]};
        }
    }
    return {legal_actions.back(), probs.back()};
}

// MCCFR outcome sampling - samples single path through tree
ld mccfr_outcome_traverse(CFRAgent& agent, str history, int c1, int c2,
                          ld pi, ld pi_opp, ld pi_sample,
                          bool is_p1_turn, ld bet1, ld bet2) {
    char last = history.empty() ? ' ' : history.back();
    if (last == 'c' || last == 'f') {
        ld payoff = get_terminal_payoff(last, c1, c2, is_p1_turn, bet1, bet2);
        return payoff / pi_sample;
    }

    int visible_card = is_p1_turn ? c2 : c1;
    str key = to_string(visible_card) + " " + history;

    InfoSet& info = agent.get_or_create(key);
    info.compute_strategy();
    vld& s = info.strategy;

    bool first_action = (history.length() <= 2);
    vi legal = get_legal_actions(is_p1_turn, bet1, bet2, first_action);

    if (legal.empty()) return 0;

    const ld epsilon = 0.6;
    int sampled_action;
    ld sample_prob;

    if (rng_uniform() < epsilon) {
        int idx = rng_int(0, (int)legal.size() - 1);
        sampled_action = legal[idx];
        sample_prob = epsilon / legal.size() + (1 - epsilon) * s[sampled_action];
    } else {
        auto [a, p] = sample_action_with_prob(s, legal);
        sampled_action = a;
        sample_prob = epsilon / legal.size() + (1 - epsilon) * p;
    }

    str new_history = history + ACTION_NAMES[sampled_action];
    ld new_bet1 = bet1, new_bet2 = bet2;
    apply_action(sampled_action, is_p1_turn, new_bet1, new_bet2);

    ld new_pi = is_p1_turn ? pi * s[sampled_action] : pi;
    ld new_pi_opp = is_p1_turn ? pi_opp : pi_opp * s[sampled_action];
    ld new_pi_sample = pi_sample * sample_prob;

    ld util = -mccfr_outcome_traverse(agent, new_history, c1, c2,
                                       new_pi, new_pi_opp, new_pi_sample,
                                       !is_p1_turn, new_bet1, new_bet2);

    ld W = util * pi_sample;

    for (int a : legal) {
        if (a == sampled_action) {
            ld regret = (W - W * s[sampled_action]) * pi_opp;
            info.regret_sum[a] += regret / sample_prob;
        } else {
            ld regret = -W * s[a] * pi_opp;
            info.regret_sum[a] += regret;
        }
    }

    for (int a : legal) {
        info.strategy_sum[a] += pi * s[a];
    }

    return util;
}

void mccfr_iteration(CFRAgent& agent) {
    int c1 = rng_int(0, NUM_RANKS - 1);
    int c2 = rng_int(0, NUM_RANKS - 1);
    mccfr_outcome_traverse(agent, "rr", c1, c2, 1.0L, 1.0L, 1.0L, true, 0.5L, 1.0L);
}

struct SimResult {
    ld total_chips;
    ld total_hands;
    ld avg_chips_per_hand;
};

// Play single hand using average strategies
ld play_hand(CFRAgent& agent1, CFRAgent& agent2, int c1, int c2) {
    str history = "rr";
    bool is_p1_turn = true;
    ld bet1 = 0.5, bet2 = 1;

    while (true) {
        char last = history.back();
        if (last == 'c' || last == 'f') {
            return get_terminal_payoff(last, c1, c2, is_p1_turn, bet1, bet2);
        }

        int visible_card = is_p1_turn ? c2 : c1;
        str key = to_string(visible_card) + " " + history;

        CFRAgent& current = is_p1_turn ? agent1 : agent2;
        InfoSet& info = current.get_or_create(key);

        int action = info.sample_action();
        bool first_action = (history.length() <= 2);
        int attempts = 0;
        while (!is_legal(action, is_p1_turn, bet1, bet2, first_action) && attempts < 100) {
            action = info.sample_action();
            attempts++;
        }
        if (attempts >= 100) action = 0;

        history += ACTION_NAMES[action];
        apply_action(action, is_p1_turn, bet1, bet2);
        is_p1_turn = !is_p1_turn;
    }
}

// Head-to-head evaluation over all card combinations
SimResult simulate(CFRAgent& agent1, CFRAgent& agent2, int rounds) {
    ld chips = 0;
    ld hands = 0;

    forr(r, 0, rounds) {
        forr(i, 0, 52) {
            forr(j, 0, 52) {
                if (i == j) continue;
                int c1 = i / 4;
                int c2 = j / 4;
                chips += play_hand(agent1, agent2, c1, c2);
                hands++;
            }
        }

        forr(i, 0, 52) {
            forr(j, 0, 52) {
                if (i == j) continue;
                int c1 = i / 4;
                int c2 = j / 4;
                chips -= play_hand(agent2, agent1, c1, c2);
                hands++;
            }
        }
    }

    return {chips, hands, chips / hands};
}

int train_cfr_timed(CFRAgent& agent, int time_ms, vector<pair<int, ld>>& curve) {
    cout << "Training CFR...";
    auto start = chrono::high_resolution_clock::now();
    auto end_time = start + chrono::milliseconds(time_ms);

    ld ev = 0;
    int iterations = 0;

    while (chrono::high_resolution_clock::now() < end_time) {
        ev += cfr_iteration(agent);
        iterations++;
        if (iterations % 10 == 0) {
            curve.push_back({iterations, ev / iterations});
        }
    }
    cout << " " << iterations << " iters\n";
    return iterations;
}

int train_mccfr_timed(CFRAgent& agent, int time_ms, vector<pair<int, ld>>& curve) {
    cout << "Training MCCFR...";
    auto start = chrono::high_resolution_clock::now();
    auto end_time = start + chrono::milliseconds(time_ms);

    int iterations = 0;

    while (chrono::high_resolution_clock::now() < end_time) {
        mccfr_iteration(agent);
        iterations++;
        if (iterations % 10000 == 0) {
            curve.push_back({iterations, 0});
        }
    }
    cout << " " << iterations << " iters\n";
    return iterations;
}

void train_cfr(CFRAgent& agent, int iterations, vector<pair<int, ld>>& curve) {
    cout << "Training " << agent.name << " (CFR) for " << iterations << " iterations...\n";
    ld ev = 0;
    forr(i, 0, iterations) {
        ev += cfr_iteration(agent);
        if ((i + 1) % 10 == 0) {
            curve.push_back({(i + 1) * 169, ev / (i + 1)});
        }
    }
    cout << "  Final avg EV: " << (ev / iterations) << "\n";
}

void train_mccfr(CFRAgent& agent, int iterations, vector<pair<int, ld>>& curve) {
    cout << "Training " << agent.name << " (MCCFR) for " << iterations << " iterations...\n";
    forr(i, 0, iterations) {
        mccfr_iteration(agent);
        if ((i + 1) % 10000 == 0) {
            curve.push_back({i + 1, 0});
        }
    }
    cout << "  Done.\n";
}

struct Args {
    int time_ms = 1000;
    int sim_rounds = 100;
    int seed = 42;
    str prefix = "indian";
};

void parse_args(int argc, char** argv, Args& args) {
    for (int i = 1; i < argc; i++) {
        string s(argv[i]);
        auto need = [&](int i) {
            if (i + 1 >= argc) { cerr << "Missing value for " << s << "\n"; exit(1); }
        };

        if (s == "--time_ms") { need(i); args.time_ms = atoi(argv[++i]); }
        else if (s == "--sim_rounds") { need(i); args.sim_rounds = atoi(argv[++i]); }
        else if (s == "--seed") { need(i); args.seed = atoi(argv[++i]); }
        else if (s == "--prefix") { need(i); args.prefix = argv[++i]; }
        else if (s == "--help" || s == "-h") {
            cout << "Indian Poker Solver: CFR vs MCCFR (Time-Based Comparison)\n";
            cout << "Usage: ./indian_poker_solver [options]\n";
            cout << "Options:\n";
            cout << "  --time_ms N      Training time in ms for EACH method (default: 1000)\n";
            cout << "  --sim_rounds N   Simulation rounds (default: 100)\n";
            cout << "  --seed N         Random seed (default: 42)\n";
            cout << "  --prefix S       Output file prefix (default: indian)\n";
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

    cout << "Indian Poker: CFR vs MCCFR\n";
    cout << "Seed: " << args.seed << ", Time: " << args.time_ms << " ms, Sim rounds: " << args.sim_rounds << "\n\n";

    CFRAgent cfr_agent("CFR");
    CFRAgent mccfr_agent("MCCFR");

    vector<pair<int, ld>> cfr_curve, mccfr_curve;

    int cfr_iters = train_cfr_timed(cfr_agent, args.time_ms, cfr_curve);
    int mccfr_iters = train_mccfr_timed(mccfr_agent, args.time_ms, mccfr_curve);

    cout << "Iteration ratio: " << (mccfr_iters / (double)max(1, cfr_iters)) << "x (MCCFR samples one path, CFR traverses full tree)\n";

    SimResult cfr_v_cfr_1 = simulate(cfr_agent, cfr_agent, args.sim_rounds);
    SimResult mccfr_v_mccfr_1 = simulate(mccfr_agent, mccfr_agent, args.sim_rounds);

    SimResult mccfr_v_cfr = simulate(mccfr_agent, cfr_agent, args.sim_rounds);
    SimResult cfr_v_mccfr = simulate(cfr_agent, mccfr_agent, args.sim_rounds);

    ld mccfr_advantage = mccfr_v_cfr.avg_chips_per_hand;

    cout << "\nSelf-play (sanity check):\n";
    cout << "CFR vs CFR: " << cfr_v_cfr_1.avg_chips_per_hand << " chips/hand\n";
    cout << "MCCFR vs MCCFR: " << mccfr_v_mccfr_1.avg_chips_per_hand << " chips/hand\n";

    cout << "\nHead-to-head:\n";
    cout << "MCCFR vs CFR: " << mccfr_advantage << " chips/hand\n";
    if (mccfr_advantage > 0.001) {
        cout << "Winner: MCCFR\n";
    } else if (mccfr_advantage < -0.001) {
        cout << "Winner: CFR\n";
    } else {
        cout << "Result: Tie\n";
    }

    ofstream resultsCSV(args.prefix + "_results.csv");
    resultsCSV << "matchup,p1,p2,total_chips,total_hands,avg_chips_per_hand\n";
    resultsCSV << "cfr_self,CFR,CFR," << cfr_v_cfr_1.total_chips << "," << cfr_v_cfr_1.total_hands << "," << cfr_v_cfr_1.avg_chips_per_hand << "\n";
    resultsCSV << "mccfr_self,MCCFR,MCCFR," << mccfr_v_mccfr_1.total_chips << "," << mccfr_v_mccfr_1.total_hands << "," << mccfr_v_mccfr_1.avg_chips_per_hand << "\n";
    resultsCSV << "mccfr_vs_cfr,MCCFR,CFR," << mccfr_v_cfr.total_chips << "," << mccfr_v_cfr.total_hands << "," << mccfr_v_cfr.avg_chips_per_hand << "\n";
    resultsCSV << "cfr_vs_mccfr,CFR,MCCFR," << cfr_v_mccfr.total_chips << "," << cfr_v_mccfr.total_hands << "," << cfr_v_mccfr.avg_chips_per_hand << "\n";
    resultsCSV.close();

    ofstream cfr_csv(args.prefix + "_cfr_training.csv");
    cfr_csv << "effective_iters,avg_ev\n";
    for (auto& p : cfr_curve) {
        cfr_csv << p.first << "," << p.second << "\n";
    }
    cfr_csv.close();

    ofstream stratCSV(args.prefix + "_strategies.csv");
    stratCSV << "agent,visible_card,history,fold,call,r3,r5,r10,shove\n";

    vector<str> key_histories = {"rr", "rrf", "rrc", "rrr3", "rrs"};
    for (int card = 0; card < 13; card++) {
        for (auto& hist : key_histories) {
            str key = to_string(card) + " " + hist;

            if (cfr_agent.nodes.count(key)) {
                vld s = cfr_agent.nodes[key].get_average_strategy();
                stratCSV << "CFR," << card << "," << hist;
                forr(a, 0, ACTIONS) stratCSV << "," << s[a];
                stratCSV << "\n";
            }

            if (mccfr_agent.nodes.count(key)) {
                vld s = mccfr_agent.nodes[key].get_average_strategy();
                stratCSV << "MCCFR," << card << "," << hist;
                forr(a, 0, ACTIONS) stratCSV << "," << s[a];
                stratCSV << "\n";
            }
        }
    }
    stratCSV.close();

    cout << "\nOutput files:\n";
    cout << "  " << args.prefix << "_results.csv\n";
    cout << "  " << args.prefix << "_cfr_training.csv\n";
    cout << "  " << args.prefix << "_strategies.csv\n";

    return 0;
}
