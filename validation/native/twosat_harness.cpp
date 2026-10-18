// Native 2-SAT harness (plan R8 item 2): runs the product solvers of native/selfmodgraph.cpp on the vectors written by
// validation/TwoSatVectors.lean and compares verdicts, checks the returned assignment against the formula, and compares
// the number of solutions enumerated by alltwosat. Mechanical evidence only.
#define main product_main
#include "../../native/selfmodgraph.cpp"
#undef main

#include <set>

static bool checkAssignment(const std::vector<std::pair<int, int>>& cs, const std::vector<int>& sol)
{
    std::set<int> s(sol.begin(), sol.end());
    for (int v : sol) if (s.count(-v)) return false;
    for (auto& c : cs) if (!s.count(c.first) && !s.count(c.second)) return false;
    return true;
}

static long countSolutions(const std::vector<std::pair<int, int>>& cs,
    std::function<std::vector<int>(std::vector<std::pair<int, int>>)> f)
{
    std::stringstream buf;
    std::streambuf* old = std::cout.rdbuf(buf.rdbuf());
    alltwosat(cs, false, f, 1000);
    std::cout.rdbuf(old);
    std::string t = buf.str();
    size_t p = t.find("Number of solutions: ");
    return p == std::string::npos ? -1 : std::stol(t.substr(p + 21));
}

int main(int argc, char** argv)
{
    if (argc < 2) { std::cerr << "usage: twosat_harness vectors.txt [maxcount-formulas]\n"; return 2; }
    std::ifstream in(argv[1]);
    std::string line;
    long total = 0, bad = 0, countsChecked = 0;
    std::vector<std::pair<std::string, std::function<std::vector<int>(std::vector<std::pair<int, int>>)>>> solvers = {
        {"twosat", twosat},
#if defined(_M_X64) || defined(__amd64__)
        {"selfmodtwosatasm", selfmodtwosatasm}, // executes the x86-64 self-modifying blueprint
#endif
#ifdef USE_VM
        {"selfmodvmtwosat", selfmodvmtwosat},
#endif
    };
    while (std::getline(in, line)) {
        if (line.empty()) continue;
        size_t a = line.find('|'), b = line.find('|', a + 1), c = line.find('|', b + 1);
        std::string id = line.substr(0, a), body = line.substr(a + 1, b - a - 1), verdict = line.substr(b + 1, c - b - 1),
            cnt = line.substr(c + 1);
        std::vector<std::pair<int, int>> cs;
        std::stringstream ss(body);
        std::string item;
        while (std::getline(ss, item, ';')) {
            size_t k = item.find(',');
            cs.push_back({ std::stoi(item.substr(0, k)), std::stoi(item.substr(k + 1)) });
        }
        bool sat = verdict == "SAT";
        { // L01: the components partition the nodes (no node is emitted twice)
            auto g = gettwosatgraph(cs);
            auto comps = tarjan_scc(g);
            std::map<int, int> seen;
            for (auto& comp : comps) for (int v : comp) seen[v]++;
            bool part = seen.size() == g.size();
            for (auto& kv : seen) if (kv.second != 1) part = false;
            total++;
            if (!part) { bad++; std::cout << "FAIL tarjan_scc partition formula " << id << std::endl; }
        }
        for (auto& s : solvers) {
            total++;
            std::vector<int> sol = s.second(cs);
            bool okv = (!sol.empty()) == sat;
            bool oka = !sat || checkAssignment(cs, sol);
            bool okc = true;
            if (cnt != "?" && std::stoi(id) <= 400) {
                long want = (std::min)(std::stol(cnt), 1000L);
                okc = countSolutions(cs, s.second) == want;
                countsChecked++;
            }
            if (!(okv && oka && okc)) {
                bad++;
                std::cout << "FAIL " << s.first << " formula " << id << " verdict=" << okv << " assignment=" << oka
                          << " count=" << okc << std::endl;
            }
        }
    }
    std::cout << "SUMMARY runs=" << total << " failures=" << bad << " countchecks=" << countsChecked << std::endl;
    return bad == 0 ? 0 : 1;
}

void test_irreducible() {}
