// selfmodgraph.cpp : This file contains the 'main' function. Program execution begins and ends there.
//
#if defined(_WIN32) || defined(_WIN64)
#define _CRT_SECURE_NO_WARNINGS
#include <windows.h> //#include <memoryapi.h>
#else
//g++ selfmodgraph.cpp -o selfmodgraph
//g++ selfmodgraph.cpp -o selfmodgraph -m32
//clang++-7 -pthread -std=c++17 -o main main.cpp
//clang++-7 -pthread -std=c++17 -o main main.cpp -m32
#include <sys/mman.h>
#endif
#include <iostream>
#include <memory>
#include <vector>
#include <map>
#include <algorithm>
#include <stack>
#include <functional>
#include <unordered_set>
#include <cassert>
#include <chrono>
#include <fstream>
#include <sstream>
#include <string>
#include <iomanip>
#include <cstring>
//O(m+n)
//https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
std::vector<std::vector<int>> tarjan_scc(std::map<int, std::vector<int>> succ)
{
    struct sccstack
    {
        int index;
        int lowlink;
        bool onstack;
    };
    std::map<int, sccstack> nodes;
    std::stack<int> s;
    std::vector<std::vector<int>> sccs;
    int index = 0;
    std::function<void(int)> strongconnect = [&index, &nodes, &s, &sccs, &succ, &strongconnect](int v) {
        nodes.insert(std::pair<int, sccstack>(v, { index, index++, true }));
        s.push(v);
        std::for_each(succ[v].begin(), succ[v].end(), [&v, &nodes, &strongconnect](int w) {
            if (nodes.find(w) == nodes.end()) {
                strongconnect(w);
                if (nodes[w].lowlink < nodes[v].lowlink) nodes[v].lowlink = nodes[w].lowlink;
            } else if (nodes[w].onstack)
                if (nodes[w].index < nodes[v].lowlink) nodes[v].lowlink = nodes[w].index;
            });
        if (nodes[v].lowlink == nodes[v].index) {
            int w;
            std::vector<int> vec;
            do {
                w = s.top(); s.pop();
                nodes[w].onstack = false;
                vec.push_back(w);
            } while (w != v);
            sccs.push_back(vec);
        }
    };
    std::for_each(succ.begin(), succ.end(), [&nodes, &strongconnect](std::pair<const int, std::vector<int>> p) {
        if (nodes.find(p.first) == nodes.end()) strongconnect(p.first);
        });
    return sccs;
}

//(x ^ y) implies -x -> y and -y -> x
std::map<int, std::vector<int>> gettwosatgraph(std::vector<std::pair<int, int>> clauses)
{
    std::map<int, std::vector<int>> succ;
    std::for_each(clauses.begin(), clauses.end(), [&succ](std::pair<int, int> xy) {
        int x = xy.first, y = xy.second;
        if (succ.find(-x) == succ.end()) {
            succ.insert(std::pair<int, std::vector<int>>(-x, std::vector<int>()));
            succ.insert(std::pair<int, std::vector<int>>(x, std::vector<int>()));
        }
        if (succ.find(-y) == succ.end()) {
            succ.insert(std::pair<int, std::vector<int>>(-y, std::vector<int>()));
            succ.insert(std::pair<int, std::vector<int>>(y, std::vector<int>()));
        }
        succ[-x].push_back(y);
        if (x != y) succ[-y].push_back(x);
        });
    return succ;
}

std::vector<int> twosat(std::vector<std::pair<int, int>> clauses)
{
    std::map<int, std::vector<int>> succ = gettwosatgraph(clauses);
    std::vector<std::vector<int>> sccs = tarjan_scc(succ);
    bool unsat = false;
    std::unordered_set<int> sol;
    std::for_each(sccs.begin(), sccs.end(), [&sol, &unsat](std::vector<int> p) {
        std::unordered_set<int> u;
        std::for_each(p.begin(), p.end(), [&sol, &unsat, &u](int v) {
            if (unsat) return;
            if (u.find(-v) != u.end()) { unsat = true; return; }
            u.insert(v);
            if (sol.find(-v) == sol.end()) sol.insert(v);
            });
        });
    std::vector<int> solv;
    if (unsat) return solv;
    solv.insert(solv.begin(), sol.begin(), sol.end());
    std::sort(solv.begin(), solv.end(), [](int x, int y) { return abs(x) < abs(y); });
    return solv;
}

void printtwosat(std::vector<int> solv)
{
    if (solv.size() == 0) std::cout << "Unsatisfiable" << std::endl;
    else {
        std::for_each(solv.begin(), solv.end(), [&solv](int v) {
            if (solv.back() != v)
                std::cout << v << " ";
            else std::cout << v << std::endl;
            });
    }
}

void alltwosat(std::vector<std::pair<int, int>> clauses, bool print,
    std::function<std::vector<int>(std::vector<std::pair<int, int>>)> f, int maxNum)
{
    //toggle bits with (-x, -x)
    //prevent duplicates with (y, y)
    std::vector<int> solv = f(clauses);
    std::stack<std::pair<std::vector<int>, size_t>> s;
    if (solv.size() != 0) s.push(std::pair<std::vector<int>, size_t>(solv, 0));
    //else std::cout << "No solutions" << std::endl;
    int count = 0;
    while (!s.empty() && count != maxNum) {
        std::pair<std::vector<int>, size_t> p = s.top(); s.pop();
        count++;
        if (print) printtwosat(p.first);
        for (size_t i = p.second; i < p.first.size(); i++) {
            std::vector<std::pair<int, int>> clausesinner;
            clausesinner.insert(clausesinner.begin(), clauses.begin(), clauses.end());
            for (size_t j = 0; j < i; j++) {
                clausesinner.push_back(std::pair<int, int>(p.first[j], p.first[j]));
            }
            clausesinner.push_back(std::pair<int, int>(-p.first[i], -p.first[i]));
            std::vector<int> solin = f(clausesinner);
            if (solin.size() != 0) s.push(std::pair<std::vector<int>, size_t>(solin, i + 1));
        }
    }
    std::cout << "Number of solutions: " << count << std::endl;
}

void parseasmlisting(const char* filename)
{
    std::ifstream fs(filename);
    std::string line;
    std::vector<std::string> offsvec;
    unsigned long offset = 0;
    unsigned long procbase = -1;
    if (fs.is_open()) {
        bool lastgood = false;
        while (std::getline(fs, line)) {
            int p1 = 0, p2 = 0;
            size_t fno = line.find_first_not_of(" \t");
            bool iscontinuation = lastgood && fno != std::string::npos && std::string(line.begin(), line.begin() + fno).compare("\t   ") == 0;
            if (iscontinuation || sscanf(line.c_str(), "%n%*X%n%*1s", &p1, &p2) == 0 && p1 == 0 && p2 == 9) {
                size_t cpos;
                std::string comment;
                std::ostringstream os;
                size_t increments = -1;
                if ((cpos = line.find(';')) != std::string::npos) {
                    comment = line.substr(cpos + 1);
                }
                if (line.find(" proc") != std::string::npos)
                {
                    if (procbase != -1) {
                        std::cout << "    };" << std::endl;
                        std::for_each(offsvec.begin(), offsvec.end(), [](std::string s) { std::cout << s << std::endl; });
                        offsvec.clear();
                    }
                    std::istringstream iss(line);
                    iss >> std::hex >> procbase;
                    std::string name;
                    iss >> name;
                    std::cout << "    unsigned char " << name << "[] = {" << std::endl;
                }
                if (!iscontinuation) line.erase(line.begin() + line.find('\t', 0), line.end());
                std::istringstream iss(line);
                if (!iscontinuation) iss >> std::hex >> offset;
                if ((cpos = comment.find('%')) != std::string::npos) { //%<variable name>%<offset increments>%\00
                    std::string offstr = comment.substr(cpos + 1);
                    comment = comment.substr(0, cpos);
                    cpos = offstr.find('%');
                    assert(cpos != std::string::npos);
                    std::istringstream is(offstr.substr(cpos + 1, offstr.size() - cpos - 1 - 1));
                    is >> increments;
                    os << "    const size_t " << offstr.substr(0, cpos) << " = 0x" << std::hex << std::setfill('0') << std::setw(sizeof(unsigned long)*2) << (offset - procbase);
                    if (increments == 0) {
                        os << ";"; increments--;
                        offsvec.push_back(os.str());
                    }
                }
                if (!iss.eof()) {
                    std::cout << "\t";
                    while (!iss.eof()) {
                        std::string b;
                        iss >> b;
                        if (b.size() == sizeof(unsigned char) * 2 + 1) {
                            assert(b[2] == '|' || b[2] == '/' || b[2] == '&');
                            b.erase(b.begin() + 2, b.end());
                            offset += sizeof(b.size()/2); std::cout << "0x" << b << ", ";
                            if (increments >= 0) {
                                increments--; os << " + sizeof(unsigned char)";
                            }
                        }
                        else if (b.size() == sizeof(unsigned long long) * 2) {
                            std::cout << "0x" << std::string(b.begin() + 14, b.end()).c_str() << ", "
                                << "0x" << std::string(b.begin() + 12, b.begin() + 14).c_str() << ", "
                                << "0x" << std::string(b.begin() + 10, b.begin() + 12).c_str() << ", "
                                << "0x" << std::string(b.begin() + 8, b.begin() + 10).c_str() << ", "
                                << "0x" << std::string(b.begin() + 6, b.begin() + 8).c_str() << ", "
                                << "0x" << std::string(b.begin() + 4, b.begin() + 6).c_str() << ", "
                                << "0x" << std::string(b.begin() + 2, b.begin() + 4).c_str() << ", "
                                << "0x" << std::string(b.begin() + 0, b.begin() + 2).c_str() << ", ";
                            offset += sizeof(b.size() / 2);
                            if (increments >= 0) {
                                increments--; os << " + sizeof(unsigned long long)";
                            }
                        }
                        else if (b.size() == sizeof(unsigned long) * 2) {
                            std::cout << "0x" << std::string(b.begin() + 6, b.end()).c_str() << ", "
                                << "0x" << std::string(b.begin() + 4, b.begin() + 6).c_str() << ", "
                                << "0x" << std::string(b.begin() + 2, b.begin() + 4).c_str() << ", "
                                << "0x" << std::string(b.begin() + 0, b.begin() + 2).c_str() << ", ";
                            offset += sizeof(b.size() / 2);
                            if (increments >= 0) {
                                increments--; os << " + sizeof(unsigned long)";
                            }
                        }
                        else if (b.size() == sizeof(unsigned short) * 2) {
                            std::cout << "0x" << std::string(b.begin() + 2, b.begin() + 4).c_str() << ", "
                                << "0x" << std::string(b.begin() + 0, b.begin() + 2).c_str() << ", ";
                            offset += sizeof(b.size() / 2);
                            if (increments >= 0) {
                                increments--; os << " + sizeof(unsigned short)";
                            }
                        }
                        else if (b.size() == sizeof(unsigned char) * 2) {
                            offset += sizeof(b.size() / 2); std::cout << "0x" << b << ", ";
                            if (increments >= 0) {
                                increments--; os << " + sizeof(unsigned char)";
                            }
                        }
                        else if (b.size() == sizeof(unsigned char)) {
                            assert(b[0] == 'E' || b[0] == 'R');
                        }
                        else {
                            assert(false);
                        }
                        if (increments == 0) {
                            os << ";"; increments--;
                            offsvec.push_back(os.str());
                        }
                    }
                    lastgood = true;
                    std::cout << std::endl;
                }
                else lastgood = false;
            }
            else lastgood = false;
        }
        fs.close();
    }
    std::cout << "    };" << std::endl;
    std::for_each(offsvec.begin(), offsvec.end(), [](std::string s) { std::cout << s << std::endl; });
}

std::vector<int> selfmodtwosatasm(std::vector<std::pair<int, int>> clauses)
{
    std::map<int, std::vector<int>> succ = gettwosatgraph(clauses);
    std::unordered_set<int> sol;
#if defined(_M_X64) || defined(__amd64__)
#if defined(_WIN32) || defined(_WIN64)
    unsigned char blueprint[] = {
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x8B, 0x01,
        0x48, 0x89, 0x05,
        0xE4, 0xFF, 0xFF, 0xFF,
        0x48, 0x89, 0x05,
        0x59, 0x01, 0x00, 0x00,
        0x48, 0xFF, 0xC0,
        0x48, 0x89, 0x01,
        0x58,
        0x48, 0x8D, 0x64, 0x24,
        0xF8,
        0x48, 0x89, 0x05,
        0x55, 0x01, 0x00, 0x00,
        0x48, 0x89, 0x25,
        0xB5, 0x00, 0x00, 0x00,
        0x48, 0x89, 0x25,
        0x64, 0x00, 0x00, 0x00,
        0xC7, 0x05, 0xBA, 0xFF, 0xFF, 0xFF,
        0xC2, 0x08, 0x00, 0x90,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x83, 0xF8, 0x00,
        0x0F, 0x84, 0x8E, 0x00, 0x00, 0x00,
        0x48, 0xFF, 0xC8,
        0x48, 0x89, 0x05,
        0xE4, 0xFF, 0xFF, 0xFF,
        0x48, 0x8B, 0xD0,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x8D, 0x64, 0x24,
        0xE0,
        0xFF, 0xD0,
        0x48, 0x8D, 0x64, 0x24,
        0x20,
        0xC6, 0x40, 0x30, 0x08,
        0x81, 0x78, 0x0A, 0xC2, 0x08,
        0x00, 0x90,
        0x74, 0x0A,
        0xC7, 0x80, 0x86, 0x01, 0x00, 0x00,
        0xEB, 0x03, 0x90, 0x90,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x3B, 0xCC,
        0x75, 0x0F,
        0xC7, 0x40, 0x2C, 0x48, 0x8B,
        0x04, 0x24,
        0xC6, 0x40, 0x2B, 0x90,
        0xC6, 0x40, 0x30, 0x90,
        0x48, 0x8D, 0x64, 0x24,
        0xF8,
        0xFF, 0xD0,
        0x48, 0x3B, 0x05,
        0xAA, 0x00, 0x00, 0x00,
        0x0F, 0x8D, 0x76, 0xFF, 0xFF, 0xFF,
        0x48, 0x89, 0x05,
        0x9D, 0x00, 0x00, 0x00,
        0xB9, 0xEB, 0x6C, 0x00, 0x00,
        0x66, 0x89, 0x0D,
        0x21, 0x00, 0x00, 0x00,
        0xE9, 0x5E, 0xFF, 0xFF, 0xFF,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x3B, 0xCC,
        0x75, 0x0D,
        0x48, 0x8D, 0x05,
        0xC5, 0xFF, 0xFF, 0xFF,
        0x48, 0x8D, 0x64, 0x24,
        0xF8,
        0x50,
        0x90, 0x90,
        0x58,
        0x48, 0x8D, 0x64, 0x24,
        0x08,
        0x48, 0x2D,
        0xCD, 0x00, 0x00, 0x00,
        0x48, 0xBA,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x8B, 0x0A,
        0x48, 0x05,
        0x97, 0x01, 0x00, 0x00,
        0x48, 0x89, 0x41, 0x02,
        0x48, 0xFF, 0xC0,
        0x48, 0xFF, 0xC0,
        0x48, 0x8D, 0x0D,
        0xC0, 0xFE, 0xFF, 0xFF,
        0x48, 0x89, 0x08,
        0x48, 0xFF, 0xC8,
        0x48, 0xFF, 0xC8,
        0x48, 0x2D,
        0x97, 0x01, 0x00, 0x00,
        0x48, 0x05,
        0xF1, 0x01, 0x00, 0x00,
        0x48, 0x89, 0x02,
        0x48, 0x2D,
        0xF1, 0x01, 0x00, 0x00,
        0x48, 0xFF, 0xC0,
        0x48, 0xFF, 0xC0,
        0x48, 0xBA,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x89, 0x10,
        0x48, 0xFF, 0xC8,
        0x48, 0xFF, 0xC8,
        0x48, 0x3B, 0xC8,
        0x75, 0x94,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x8D, 0x64, 0x24,
        0x08,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xE1,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0x39, 0x05,
        0xF1, 0xFF, 0xFF, 0xFF,
        0x75, 0x16,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xE0,
        0x48, 0xC7, 0xC1,
        0x00, 0x00, 0x00, 0x00,
        0x48, 0x8D, 0x64, 0x24,
        0xD8,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xD0,
        0x48, 0x8D, 0x64, 0x24,
        0x28,
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xE0,
    };
    const size_t indexoffs = 0x0000000a + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t counteroffs = 0x00000050 + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t getsuccnodeaddroffs = 0x00000071 + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t getsuccnodeaddroppoffs = 0x0000007b + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t starttopooffs = 0x0000011c + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t succsizeoffs = 0x00000164 + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t checksamesccoffs = 0x000001a1 + sizeof(unsigned char) + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t unsatoffs = 0x000001aa + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t unsatoppoffs = 0x000001b4 + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t addsolutionoffs = 0x000001cc + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t addsolutionoppoffs = 0x000001d6 + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t satoffs = 0x000001e7 + sizeof(unsigned char) + sizeof(unsigned char);
    const size_t satoppoffs = 0x000001f1 + sizeof(unsigned char) + sizeof(unsigned char);
    unsigned char callblueprint[] = {
        0x48, 0xB8,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0x81, 0x78, 0x0A,
        0xC2, 0x08, 0x00, 0x90,
        0x74, 0x02,
        0xFF, 0xD0,
    };
    const size_t callblueprintoffs = 0x00000000 + sizeof(unsigned char) + sizeof(unsigned char);
    unsigned char jumptopo[] = {
        0x48, 0xB9,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xE1,
    };
    const size_t jumptopooffs = 0x00000000 + sizeof(unsigned char) + sizeof(unsigned char);
#else
unsigned char blueprint[] = {
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0xB9,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x8B, 0x01,
    0x48, 0x89, 0x05,
    0xE4, 0xFF, 0xFF, 0xFF,
    0x48, 0x89, 0x05,
    0x4B, 0x01, 0x00, 0x00,
    0x48, 0xFF, 0xC0,
    0x48, 0x89, 0x01,
    0x58,
    0x48, 0x8D, 0x64, 0x24,
    0xF8,
    0x48, 0x89, 0x05,
    0x47, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x25,
    0xA7, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x25,
    0x5A, 0x00, 0x00, 0x00,
    0xC7, 0x05, 0xBA, 0xFF, 0xFF, 0xFF,
    0xC2, 0x08, 0x00, 0x90,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x83, 0xF8, 0x00,
    0x0F, 0x84, 0x80, 0x00, 0x00, 0x00,
    0x48, 0xFF, 0xC8,
    0x48, 0x89, 0x05,
    0xE4, 0xFF, 0xFF, 0xFF,
    0x48, 0x8B, 0xF0,
    0x48, 0xBF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0xC6, 0x40, 0x30, 0x08,
    0x81, 0x78, 0x0A, 0xC2, 0x08,
    0x00, 0x90,
    0x74, 0x0A,
    0xC7, 0x80, 0x78, 0x01, 0x00, 0x00,
    0xEB, 0x03, 0x90, 0x90,
    0x48, 0xB9,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x3B, 0xCC,
    0x75, 0x0F,
    0xC7, 0x40, 0x2C, 0x48, 0x8B,
    0x04, 0x24,
    0xC6, 0x40, 0x2B, 0x90,
    0xC6, 0x40, 0x30, 0x90,
    0x48, 0x8D, 0x64, 0x24,
    0xF8,
    0xFF, 0xD0,
    0x48, 0x3B, 0x05,
    0xA6, 0x00, 0x00, 0x00,
    0x7D, 0x84,
    0x48, 0x89, 0x05,
    0x9D, 0x00, 0x00, 0x00,
    0xB9, 0xEB, 0x6C, 0x00, 0x00,
    0x66, 0x89, 0x0D,
    0x21, 0x00, 0x00, 0x00,
    0xE9, 0x6C, 0xFF, 0xFF, 0xFF,
    0x48, 0xB9,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x3B, 0xCC,
    0x75, 0x0D,
    0x48, 0x8D, 0x05,
    0xC9, 0xFF, 0xFF, 0xFF,
    0x48, 0x8D, 0x64, 0x24,
    0xF8,
    0x50,
    0x90, 0x90,
    0x58,
    0x48, 0x8D, 0x64, 0x24,
    0x08,
    0x48, 0x2D,
    0xC3, 0x00, 0x00, 0x00,
    0x48, 0xBA,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x8B, 0x0A,
    0x48, 0x05,
    0x89, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x41, 0x02,
    0x48, 0xFF, 0xC0,
    0x48, 0xFF, 0xC0,
    0x48, 0x8D, 0x0D,
    0xCE, 0xFE, 0xFF, 0xFF,
    0x48, 0x89, 0x08,
    0x48, 0xFF, 0xC8,
    0x48, 0xFF, 0xC8,
    0x48, 0x2D,
    0x89, 0x01, 0x00, 0x00,
    0x48, 0x05,
    0xE3, 0x01, 0x00, 0x00,
    0x48, 0x89, 0x02,
    0x48, 0x2D,
    0xE3, 0x01, 0x00, 0x00,
    0x48, 0xFF, 0xC0,
    0x48, 0xFF, 0xC0,
    0x48, 0xBA,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x89, 0x10,
    0x48, 0xFF, 0xC8,
    0x48, 0xFF, 0xC8,
    0x48, 0x3B, 0xC8,
    0x75, 0x94,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x8D, 0x64, 0x24,
    0x08,
    0x48, 0xB9,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE1,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x39, 0x05,
    0xF1, 0xFF, 0xFF, 0xFF,
    0x75, 0x16,
    0x48, 0xBF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE0,
    0x48, 0xC7, 0xC1,
    0x00, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x64, 0x24,
    0xF8,
    0x48, 0xBF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0x48, 0x8D, 0x64, 0x24,
    0x08,
    0x48, 0xBF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE0,
};
const size_t indexoffs = 0x0000000a + sizeof(unsigned char) + sizeof(unsigned char);
const size_t counteroffs = 0x00000050 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t getsuccnodeaddroffs = 0x00000071 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t getsuccnodeaddroppoffs = 0x0000007b + sizeof(unsigned char) + sizeof(unsigned char);
const size_t starttopooffs = 0x0000010e + sizeof(unsigned char) + sizeof(unsigned char);
const size_t succsizeoffs = 0x00000156 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t checksamesccoffs = 0x00000193 + sizeof(unsigned char) + sizeof(unsigned char) + sizeof(unsigned char);
const size_t unsatoffs = 0x0000019c + sizeof(unsigned char) + sizeof(unsigned char);
const size_t unsatoppoffs = 0x000001a6 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t addsolutionoffs = 0x000001be + sizeof(unsigned char) + sizeof(unsigned char);
const size_t addsolutionoppoffs = 0x000001c8 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t satoffs = 0x000001d9 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t satoppoffs = 0x000001e3 + sizeof(unsigned char) + sizeof(unsigned char);
unsigned char callblueprint[] = {
    0x48, 0xB8,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0x81, 0x78, 0x0A,
    0xC2, 0x08, 0x00, 0x90,
    0x74, 0x02,
    0xFF, 0xD0,
};
const size_t callblueprintoffs = 0x00000000 + sizeof(unsigned char) + sizeof(unsigned char);
unsigned char jumptopo[] = {
    0x48, 0xB9,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE1,
};
const size_t jumptopooffs = 0x00000000 + sizeof(unsigned char) + sizeof(unsigned char);
#endif
const size_t fixups[] = { 0 };
#else
#if defined(_WIN32) || defined(_WIN64)
unsigned char blueprint[] = {
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0x8B, 0x01,
    0xA3, 0xF0, 0xFF, 0xFF, 0xFF,
    0xA3, 0xB6, 0x00, 0x00, 0x00,
    0x40,
    0x89, 0x01,
    0x8B, 0x04, 0x24,
    0x58,
    0xA3, 0xAF, 0x00, 0x00, 0x00,
    0x89, 0x25, 0x55, 0x00, 0x00, 0x00,
    0x89, 0x25, 0x25, 0x00, 0x00, 0x00,
    0xC6, 0x05, 0xD1, 0xFF, 0xFF, 0xFF,
    0xC3,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0x83, 0xF8, 0x00,
    0x74, 0x3D,
    0x48,
    0xA3, 0xF1, 0xFF, 0xFF, 0xFF,
    0x50,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0x3B, 0xCC,
    0x75, 0x04,
    0xC6, 0x40, 0x1C, 0x90,
    0xFF, 0xD0,
    0x3B, 0x05, 0x65, 0x00, 0x00, 0x00,
    0x7D, 0xCC,
    0xA3, 0x5E, 0x00, 0x00, 0x00,
    0xB9, 0xEB, 0x3D, 0x00, 0x00,
    0x66, 0x89, 0x0D,
    0x12, 0x00, 0x00, 0x00,
    0xEB, 0xB9,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0x3B, 0xCC,
    0x75, 0x07,
    0x8D, 0x05, 0xD6, 0xFF, 0xFF, 0xFF,
    0x50,
    0x90, 0x90,
    0x58,
    0x2D, 0x61, 0x00, 0x00, 0x00,
    0xBA, 0xFF, 0xFF, 0xFF, 0xFF,
    0x8B, 0x0A,
    0x05, 0xD7, 0x00, 0x00, 0x00,
    0x89, 0x41, 0x01,
    0x40,
    0x8D, 0x0D, 0x56, 0xFF, 0xFF, 0xFF,
    0x89, 0x08,
    0x48,
    0x2D, 0xD7, 0x00, 0x00, 0x00,
    0x05, 0x06, 0x01, 0x00, 0x00,
    0x89, 0x02,
    0x2D, 0x06, 0x01, 0x00, 0x00,
    0x40,
    0xBA, 0xFF, 0xFF, 0xFF, 0xFF,
    0x89, 0x10,
    0x48,
    0x3B, 0xC8,
    0x75, 0xC3,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE1,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0x39, 0x05, 0xF6, 0xFF, 0xFF, 0xFF,
    0x75, 0x0C,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE0,
    0xB9, 0x00, 0x00, 0x00, 0x00,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE0,
};
const size_t indexoffs = 0x00000005 + sizeof(unsigned char);
const size_t fixup1 = 0x0000000c + sizeof(unsigned char);
const size_t fixup2 = 0x00000011 + sizeof(unsigned char);
const size_t fixup3 = 0x0000001d + sizeof(unsigned char);
const size_t fixup4 = 0x00000022 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup5 = 0x00000028 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup6 = 0x0000002e + sizeof(unsigned char) + sizeof(unsigned char);
const size_t counteroffs = 0x00000035 + sizeof(unsigned char);
const size_t fixup7 = 0x00000040 + sizeof(unsigned char);
const size_t getsuccnodeaddroffs = 0x00000046 + sizeof(unsigned char);
const size_t getsuccnodeaddroppoffs = 0x0000004b + sizeof(unsigned char);
const size_t fixup8 = 0x00000061 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup9 = 0x00000069 + sizeof(unsigned char);
const size_t fixup10 = 0x00000073 + sizeof(unsigned char) + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup11 = 0x00000085 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t starttopooffs = 0x00000094 + sizeof(unsigned char);
const size_t fixup12 = 0x000000a4 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t succsizeoffs = 0x000000bf + sizeof(unsigned char);
const size_t checksamesccoffs = 0x000000dc + sizeof(unsigned char) + sizeof(unsigned char);
const size_t unsatoffs = 0x000000e4 + sizeof(unsigned char);
const size_t unsatoppoffs = 0x000000e9 + sizeof(unsigned char);
const size_t addsolutionoffs = 0x000000f5 + sizeof(unsigned char);
const size_t addsolutionoppoffs = 0x000000fa + sizeof(unsigned char);
const size_t satoffs = 0x00000101 + sizeof(unsigned char);
const size_t satoppoffs = 0x00000106 + sizeof(unsigned char);
unsigned char callblueprint[] = {
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
};
const size_t callblueprintoffs = 0x00000000 + sizeof(unsigned char);
unsigned char jumptopo[] = {
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE1,
};
const size_t jumptopooffs = 0x00000000 + sizeof(unsigned char);
#else
unsigned char blueprint[] = {
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0x8B, 0x01,
    0xA3, 0xF0, 0xFF, 0xFF, 0xFF,
    0xA3, 0xBA, 0x00, 0x00, 0x00,
    0x40,
    0x89, 0x01,
    0x8B, 0x04, 0x24,
    0x58,
    0xA3, 0xB3, 0x00, 0x00, 0x00,
    0x89, 0x25, 0x59, 0x00, 0x00, 0x00,
    0x89, 0x25, 0x29, 0x00, 0x00, 0x00,
    0xC6, 0x05, 0xD1, 0xFF, 0xFF, 0xFF,
    0xC3,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0x83, 0xF8, 0x00,
    0x74, 0x41,
    0x48,
    0xA3, 0xF1, 0xFF, 0xFF, 0xFF,
    0x50,
    0x68, 0x98, 0xBA, 0xDC, 0xFE,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0x8D, 0x64, 0x24, 0x08,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0x3B, 0xCC,
    0x75, 0x04,
    0xC6, 0x40, 0x1C, 0x90,
    0xFF, 0xD0,
    0x3B, 0x05, 0x65, 0x00, 0x00, 0x00,
    0x7D, 0xC8,
    0xA3, 0x5E, 0x00, 0x00, 0x00,
    0xB9, 0xEB, 0x3D, 0x00, 0x00,
    0x66, 0x89, 0x0D,
    0x12, 0x00, 0x00, 0x00,
    0xEB, 0xB5,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0x3B, 0xCC,
    0x75, 0x07,
    0x8D, 0x05, 0xD6, 0xFF, 0xFF, 0xFF,
    0x50,
    0x90, 0x90,
    0x58,
    0x2D, 0x65, 0x00, 0x00, 0x00,
    0xBA, 0xFF, 0xFF, 0xFF, 0xFF,
    0x8B, 0x0A,
    0x05, 0xDB, 0x00, 0x00, 0x00,
    0x89, 0x41, 0x01,
    0x40,
    0x8D, 0x0D, 0x52, 0xFF, 0xFF, 0xFF,
    0x89, 0x08,
    0x48,
    0x2D, 0xDB, 0x00, 0x00, 0x00,
    0x05, 0x0E, 0x01, 0x00, 0x00,
    0x89, 0x02,
    0x2D, 0x0E, 0x01, 0x00, 0x00,
    0x40,
    0xBA, 0xFF, 0xFF, 0xFF, 0xFF,
    0x89, 0x10,
    0x48,
    0x3B, 0xC8,
    0x75, 0xC3,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE1,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0x39, 0x05, 0xF6, 0xFF, 0xFF, 0xFF,
    0x75, 0x11,
    0x68, 0x98, 0xBA, 0xDC, 0xFE,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0x8D, 0x64, 0x24, 0x04,
    0xC3,
    0xB9, 0x00, 0x00, 0x00, 0x00,
    0x68, 0x98, 0xBA, 0xDC, 0xFE,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0x8D, 0x64, 0x24, 0x04,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE0,
};
const size_t indexoffs = 0x00000005 + sizeof(unsigned char);
const size_t fixup1 = 0x0000000c + sizeof(unsigned char);
const size_t fixup2 = 0x00000011 + sizeof(unsigned char);
const size_t fixup3 = 0x0000001d + sizeof(unsigned char);
const size_t fixup4 = 0x00000022 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup5 = 0x00000028 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup6 = 0x0000002e + sizeof(unsigned char) + sizeof(unsigned char);
const size_t counteroffs = 0x00000035 + sizeof(unsigned char);
const size_t fixup7 = 0x00000040 + sizeof(unsigned char);
const size_t getsuccnodeaddroffs = 0x00000046 + sizeof(unsigned char);
const size_t getsuccnodeaddroppoffs = 0x0000004b + sizeof(unsigned char);
const size_t fixup8 = 0x00000065 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup9 = 0x0000006d + sizeof(unsigned char);
const size_t fixup10 = 0x00000077 + sizeof(unsigned char) + sizeof(unsigned char) + sizeof(unsigned char);
const size_t fixup11 = 0x00000089 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t starttopooffs = 0x00000098 + sizeof(unsigned char);
const size_t fixup12 = 0x000000a8 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t succsizeoffs = 0x000000c3 + sizeof(unsigned char);
const size_t checksamesccoffs = 0x000000e0 + sizeof(unsigned char) + sizeof(unsigned char);
const size_t unsatoffs = 0x000000e8 + sizeof(unsigned char);
const size_t unsatoppoffs = 0x000000ed + sizeof(unsigned char);
const size_t addsolutionoffs = 0x000000fe + sizeof(unsigned char);
const size_t addsolutionoppoffs = 0x00000103 + sizeof(unsigned char);
const size_t satoppoffs = 0x0000010e + sizeof(unsigned char);
unsigned char callblueprint[] = {
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
};
const size_t callblueprintoffs = 0x00000000 + sizeof(unsigned char);
unsigned char jumptopo[] = {
    0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xE1,
    0x68, 0x98, 0xBA, 0xDC, 0xFE,
    0xB8, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xD0,
    0x8D, 0x64, 0x24, 0x04,
    0xC3,
};
const size_t jumptopooffs = 0x00000000 + sizeof(unsigned char);
const size_t satoffs = 0x00000007 + sizeof(unsigned char);
const size_t satorigoffs = 0x0000000c + sizeof(unsigned char);
#endif

    const size_t fixups[] = { fixup1, fixup2, fixup3, fixup4, fixup5, fixup6, fixup7, fixup8, fixup9, fixup10, fixup11, fixup12, checksamesccoffs };
#endif

    size_t dwSize = (size_t)(sizeof(jumptopo) + (sizeof(callblueprint) + sizeof(blueprint)) * succ.size());
    //mmap/munmap on Linux
#if defined(_WIN32) || defined(_WIN64)
    LPVOID pCodeBlock = VirtualAlloc(NULL, dwSize, MEM_COMMIT, PAGE_EXECUTE_READWRITE); // | PAGE_NOCACHE
    if (pCodeBlock == NULL) {
        assert(false); return std::vector<int>();
    }
#else
    void* pCodeBlock = mmap(NULL, dwSize, PROT_EXEC | PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    if (pCodeBlock == MAP_FAILED) {
        assert(false); return std::vector<int>();
    }
#endif
    size_t index = 0;
    void* starttopo = &((unsigned char*)pCodeBlock)[sizeof(callblueprint) * succ.size()];
    std::function<void()> sat = []() {};
    std::function<void()> unsat = [&sol]() { sol.clear(); };
    //patch jumptopo
    *((std::function<void()>**)&jumptopo[jumptopooffs]) = &sat;
    //patch blueprint
    *((size_t**)&blueprint[indexoffs]) = &index;
    *((void**)&blueprint[starttopooffs]) = &starttopo;
    *((size_t*)&blueprint[succsizeoffs]) = succ.size();
    auto fptr = &std::function<void* (int)>::operator();
    *((void**)&blueprint[getsuccnodeaddroppoffs]) = reinterpret_cast<void*&>(fptr);
    *((void**)&blueprint[unsatoffs]) = &unsat;
    auto fvptr = &std::function<void()>::operator();
    *((void**)&blueprint[unsatoppoffs]) = reinterpret_cast<void*&>(fvptr);
    *((void**)&blueprint[addsolutionoppoffs]) = reinterpret_cast<void*&>(fvptr);
#if !defined(_WIN32) && !defined(_WIN64) && !defined(_M_X64) && !defined(__amd64__)
    *((void**)&blueprint[satoppoffs]) = (unsigned char*)pCodeBlock + sizeof(callblueprint) * succ.size() + satoffs - 1;
    *((void**)&jumptopo[satoffs]) = &sat;
    *((void**)&jumptopo[satorigoffs]) = reinterpret_cast<void*&>(fvptr);
#else
    *((void**)&blueprint[satoffs]) = &sat;
    *((void**)&blueprint[satoppoffs]) = reinterpret_cast<void*&>(fvptr);
#endif
    std::memcpy((unsigned char*)pCodeBlock + sizeof(callblueprint) * succ.size(), jumptopo, sizeof(jumptopo));
    std::map<int, std::pair<std::function<void*(int)>, std::function<void()>>> getnodesuccaddrsetsol;
    std::map<int, size_t> idxmap;
    //std::function<void*(int)> testlambda = [](int x) { return (void*)NULL; };
    //testlambda(0); //rcx=testlambda, call operator()
    std::transform(succ.begin(), succ.end(), std::inserter(idxmap, idxmap.end()),
        [&idxmap](std::pair<const int, std::vector<int>> p) {
        return std::pair<int, size_t>(p.first, idxmap.size()); });    
    std::transform(succ.begin(), succ.end(), std::inserter(getnodesuccaddrsetsol, getnodesuccaddrsetsol.end()),
        [&succ, &sol, &pCodeBlock, &idxmap](std::pair<const int, std::vector<int>> p) {
            int x = p.first;
            return std::pair<int, std::pair<std::function<void* (int)>, std::function<void()>>>(
                x, std::pair<std::function<void*(int)>, std::function<void()>>(
                [&succ, &pCodeBlock, &idxmap, x](int idx) {
                        return (unsigned char*)pCodeBlock + sizeof(callblueprint) * succ.size() + sizeof(jumptopo) + sizeof(blueprint) * idxmap[succ[x][idx]]; },
                    //std::distance(succ.begin(), succ.find(succ[x][idx]))
                [&sol, x]() { if (sol.find(-x) == sol.end()) sol.insert(x); }));
        });
    std::for_each(succ.begin(), succ.end(), [&jumptopo, &callblueprint, &blueprint, &pCodeBlock, &succ,
            &getnodesuccaddrsetsol, &idxmap,
        callblueprintoffs, counteroffs, getsuccnodeaddroffs, checksamesccoffs, addsolutionoffs, fixups]
        (std::pair<const int, std::vector<int>> p) {
        size_t i = idxmap[p.first];
        unsigned char* basebp = (unsigned char*)pCodeBlock + sizeof(callblueprint) * succ.size() + sizeof(jumptopo) + sizeof(blueprint) * i;
        std::memcpy(((unsigned char*)pCodeBlock) + sizeof(callblueprint) * i, callblueprint, sizeof(callblueprint));
        *(void**)((unsigned char*)pCodeBlock + sizeof(callblueprint) * i + callblueprintoffs) =
            basebp;
        std::memcpy(basebp, blueprint, sizeof(blueprint));
        //patch blueprint per node
        *((size_t*)(basebp + counteroffs)) = succ[p.first].size();
        *((std::function<void*(int)>**)(basebp + getsuccnodeaddroffs)) =
            &getnodesuccaddrsetsol[p.first].first;
        *((int*)(basebp + checksamesccoffs)) += (int)(
            ((unsigned char*)pCodeBlock + sizeof(callblueprint) * succ.size() + sizeof(jumptopo) + sizeof(blueprint) * idxmap[-p.first]) - basebp);
        *((std::function<void()>**)(basebp + addsolutionoffs)) =
            &getnodesuccaddrsetsol[p.first].second;
#if !defined(_M_X64) && !defined(__amd64__)
        for (int j = 0; j < sizeof(fixups) / sizeof(fixups[0]); j++) {
            *((size_t*)(basebp + fixups[j])) += (size_t)basebp + fixups[j] + sizeof(size_t);
        }
#endif
        });
    //unsat(); //unsat.operator()();
    ((void(*)())pCodeBlock)();
    /*std::for_each(succ.begin(), succ.end(), [&pCodeBlock, &succ, &idxmap, checksamesccoffs](std::pair<const int, std::vector<int>> p) {
        size_t i = idxmap[p.first];
        unsigned char* basebp = (unsigned char*)pCodeBlock + sizeof(callblueprint) * succ.size() + sizeof(jumptopo) + sizeof(blueprint) * i;
        std::cout << p.first << " " << *((size_t*)(basebp + checksamesccoffs - 3 - sizeof(size_t))) << " " << *((size_t*)(basebp + checksamesccoffs + sizeof(int) + *((int*)(basebp + checksamesccoffs)))) << std::endl;
        });*/
#if defined(_WIN32) || defined(_WIN64)
    VirtualFree(pCodeBlock, 0, MEM_RELEASE);
#else
    munmap(pCodeBlock, dwSize);
#endif
    std::vector<int> solv;
    solv.insert(solv.begin(), sol.begin(), sol.end());
    std::sort(solv.begin(), solv.end(), [](int x, int y) { return abs(x) < abs(y); });
    return solv;
}

//%%label%%expression/statement/condition%%
//self-modifying language has stack instructions:
//returnjump(location, value) or returnjump(location)
//pop()/peek()/getsp()/push(expression)
//self-modifying language has control-flow or data instructions:
//modexpr(%%label%%, value)
//modsb(%%label%%statementblock%%)
std::vector<int> selfmodvmtwosathl(std::vector<std::pair<int, int>> clauses)
{
    std::map<int, std::vector<int>> succ = gettwosatgraph(clauses);
    std::unordered_set<int> sol;
    //int reg0 = %%index%%0%%;
    std::function<void()> sat = []() {};
    std::function<void()> unsat = [&sol]() { sol.clear(); };
    //reg0 = %%starttopo%%starttopoloc%%;
    std::map<int, std::function<void()>> succfunc;
    std::transform(succ.begin(), succ.end(), std::inserter(succfunc, succfunc.end()),
        [/*&index, &starttopo, */&succ, &sol, &sat, &unsat, &succfunc](std::pair<const int, std::vector<int>> p) {
        int x = p.first;
        return std::pair<int, std::function<void()>>(x, [x, /*&index, &starttopo, */&succ, &sol, &sat, &unsat, &succfunc/*, reg0*/]() {
            /*int reg0 = %%nodeaddrloc %%-1%%;
            modexpr(%%nodeaddrloc%%, *%%index%%);
            modexpr(%%lowlinkloc%%, *%%index%%);
            modexpr(%%index%%, *%%index %%+1);
            reg0 = %%peekretloc %%pop()%%;
            modexpr(%%retloc%%, reg0);
            modexpr(%%onstackloc%%, getsp());
            modexpr(%%topopstackloc%%, getsp());
            modsb(%%nodeaddrloc %%return reg0; %%);
            while (true) {
                reg0 = %%counterloc %%succ[x].size()%%;
                if (reg0 == 0) break;
                modexpr(%%counterloc%%, reg0 - 1);
                if (getsp() == %%onstackloc %%0 %%) {
                    modexpr(%%succfunc[succ[x][reg0-1]].peekretloc%%, peek());
                }
                reg0 = succfunc[succ[x][reg0-1]]();
                %% calllocp1%%;
                if (reg0 < *%%lowlinkloc%%) {
                    modexpr(%%lowlinkloc%%, reg0);
                    modexpr(%%checksccloc%%, true);
                }
            }
            if (getsp() == %%onstackloc %%0 %%) {
                push(%%calllocp1%%);
            }
            if (%%checksccloc %%false %%) {
                reg0 = pop();
                modexpr(*%%starttopo%%, reg0 + %%nodeaddrsetloc %%-%%calllocp1%%);
                modexpr(reg0 + %%nodeaddrsetloc %%-%%calllocp1%%, %% nodeaddrloc%%);
                modexpr(%%starttopo%%, reg0 + %%nexttopoloc %%-%%calllocp1%%);
                modexpr(reg0 + %%nodeaddrloc %%-%%calllocp1%%, succ.size());
            }
            reg0 = %%lowlinkloc %%-1%%;
            returnjump(%%retloc %%0 %%, reg0);
            reg0 = %%nodeaddrsetloc %%-1%%;
            if (reg0 == *%%succfunc[x].nodeaddrsetloc%%) returnjump(unsat);
            if (sol.find(-x) == sol.end()) sol.insert(x);
            returnjump(%%nexttopoloc %%sat%%);*/
        });
    });
    std::for_each(succfunc.begin(), succfunc.end(), [](std::pair<int, std::function<void()>> p) { p.second(); });
    //returnjump(%%starttopoloc%%sat%%);
    std::vector<int> solv;
    solv.insert(solv.begin(), sol.begin(), sol.end());
    std::sort(solv.begin(), solv.end(), [](int x, int y) { return abs(x) < abs(y); });
    return solv;
}

#ifdef USE_VM
std::vector<int> selfmodvmtwosat(std::vector<std::pair<int, int>> clauses)
{
    enum class opcodes
    {
        CALL = 0,
        DATA = 1,
        JMP = 2,
        LOAD = 3,
        STORE = 4,
        POP = 5,
        MODINST = 6,
        JC = 7,
        RET = 8,
        PEEK = 9,
        NOP = 10,
        FUNC = 11,
        PUSH = 12
    };
    const char* opstrs[]{ "CALL", "DATA", "JMP", "LOAD", "STORE", "POP",
        "MODINST", "JC", "RET", "PEEK", "NOP", "FUNC", "PUSH" };
    class vminstruct {
    public:
        opcodes opcode;
        vminstruct(opcodes opcode) {
            this->opcode = opcode;
        }
        virtual ~vminstruct() {}
    };
    class addrvminstruct : public vminstruct {
    public:
        std::function<size_t()> address;
        addrvminstruct(opcodes opcode, std::function<size_t()> addr) : vminstruct(opcode)
        {
            this->address = addr;
        }
    };
    class datavminstruct : public vminstruct {
    public:
        size_t data;
        datavminstruct(opcodes opcode, size_t data) : vminstruct(opcode)
        {
            this->data = data;
        }
    };
    class storevminstruct : public vminstruct {
    public:
        std::function<size_t()> data;
        std::function<size_t()> address;
        storevminstruct(opcodes opcode, std::function<size_t()> data, std::function<size_t()> addr) : vminstruct(opcode)
        {
            this->data = data;
            this->address = addr;
        }
    };
    class modinstvminstruct : public vminstruct {
    public:
        std::function<std::unique_ptr<vminstruct>()> data;
        std::function<size_t()> address;
        modinstvminstruct(opcodes opcode, std::function<std::unique_ptr<vminstruct>()> data,
            std::function<size_t()> addr) : vminstruct(opcode)
        {
            this->data = data;
            this->address = addr;
        }
    };
    class jcvminstruct : public vminstruct {
    public:
        std::function<bool()> cond;
        size_t offset;
        jcvminstruct(opcodes opcode, std::function<bool()> cond, size_t offs) : vminstruct(opcode)
        {
            this->cond = cond;
            this->offset = offs;
        }
    };
    const int SAT = -1, UNSAT = -2;
    std::map<int, std::vector<int>> succ = gettwosatgraph(clauses);
    std::unordered_set<int> sol;
    std::vector<std::unique_ptr<vminstruct>> instructions;
    std::map<int, size_t> nodeaddr;
    std::function<std::function<size_t()>(int, size_t)> makenodeaddr = [&nodeaddr](int x, size_t offset)
    {
        return [x, offset, &nodeaddr]() { return nodeaddr[x] + offset; };
    };
    size_t index = instructions.size();
    instructions.push_back(std::make_unique<datavminstruct>(opcodes::DATA, 0));
    std::for_each(succ.begin(), succ.end(), [&instructions, &makenodeaddr](std::pair<int, std::vector<int>> p) {
        instructions.push_back(std::make_unique<addrvminstruct>(opcodes::CALL, makenodeaddr(p.first, 0)));
        });
    size_t starttopo = instructions.size();
    instructions.push_back(std::make_unique<datavminstruct>(opcodes::DATA, starttopo + 1)); //topopological sort pointer
    instructions.push_back(std::make_unique<addrvminstruct>(opcodes::JMP, [SAT]() { return SAT; }));
    std::vector<std::function<std::unique_ptr<vminstruct>(int)>> blueprint;
    size_t reg0 = 0;
    std::stack<size_t> s;
    size_t nodeaddrloc = blueprint.size(), peekretloc, counterloc, callloc, loopedgeloc,
        checklowlinkloc, nextedgeloc, 
        onstackloc, checksccloc, topopstackloc, nextnodeloc, gotonextnodeloc,
        lowlinkloc, retloc, nodeaddrsetloc, checksamesccloc, satloc, nexttopoloc;
    blueprint.push_back([](int x) { return std::make_unique<datavminstruct>(opcodes::DATA, -1); });
    blueprint.push_back([index](int x) { return std::make_unique<datavminstruct>(opcodes::LOAD, index); });
    blueprint.push_back([&reg0, &makenodeaddr, nodeaddrloc](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&reg0]() { return reg0; }, makenodeaddr(x, nodeaddrloc)); });
    blueprint.push_back([&reg0, &makenodeaddr, &lowlinkloc](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&reg0]() { return reg0; }, makenodeaddr(x, lowlinkloc)); });
    blueprint.push_back([&reg0, &makenodeaddr, nodeaddrloc, index](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&reg0]() { return reg0 + 1; }, [index]() { return index; }); });
    peekretloc = blueprint.size();
    blueprint.push_back([](int x) { return std::make_unique<vminstruct>(opcodes::POP); });
    blueprint.push_back([&makenodeaddr, &retloc, &reg0](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, [&reg0]() {
            return std::make_unique<addrvminstruct>(opcodes::JMP, [](size_t reg0) { return [reg0]() { return reg0; }; }(reg0)); }, makenodeaddr(x, retloc)); });
    blueprint.push_back([&s, &makenodeaddr, &checksccloc, &onstackloc](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, [&s, &checksccloc, &onstackloc]() {
            return std::make_unique<jcvminstruct>(opcodes::JC, [&s](size_t x) {
                return [x, &s]() { return x != s.size(); }; }(s.size()),
                checksccloc - onstackloc); }, makenodeaddr(x, onstackloc)); });
    blueprint.push_back([&s, &makenodeaddr, &callloc, &topopstackloc](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, [&s, &callloc, &topopstackloc]() {
            return std::make_unique<jcvminstruct>(opcodes::JC, [&s](size_t x) {
                return [x, &s]() { return x != s.size(); }; }(s.size()),
                callloc - topopstackloc); }, makenodeaddr(x, topopstackloc)); });
    blueprint.push_back([&makenodeaddr, nodeaddrloc](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, []() {
            return std::make_unique<vminstruct>(opcodes::RET); }, makenodeaddr(x, nodeaddrloc + 1)); });
    counterloc = blueprint.size();
    blueprint.push_back([&succ](int x) { return std::make_unique<datavminstruct>(opcodes::DATA, succ[x].size()); });
    loopedgeloc = blueprint.size();
    blueprint.push_back([loopedgeloc, &onstackloc, &reg0](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, [&reg0]() { return reg0 == 0; }, onstackloc - loopedgeloc); });
    blueprint.push_back([counterloc, &reg0, &makenodeaddr](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&reg0]() { return reg0 - 1; }, makenodeaddr(x, counterloc)); });
    topopstackloc = blueprint.size();
    blueprint.push_back([callloc, topopstackloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, []() { return true; }, callloc - topopstackloc); });
    blueprint.push_back([peekretloc, &reg0, &succ, &makenodeaddr](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, []() { return std::make_unique<vminstruct>(opcodes::PEEK); },
            [&succ, &reg0, &makenodeaddr, x, peekretloc]() { return makenodeaddr(succ[x][reg0 - 1], peekretloc)(); }); });
    callloc = blueprint.size();
    blueprint.push_back([nodeaddrloc, &reg0, &succ, &makenodeaddr](int x) {
        return std::make_unique<addrvminstruct>(opcodes::CALL, [&succ, &reg0, &makenodeaddr, x, nodeaddrloc]() {
            return makenodeaddr(succ[x][reg0 - 1], nodeaddrloc)(); }); });
    checklowlinkloc = blueprint.size();
    blueprint.push_back([&reg0, &instructions, &nodeaddr, counterloc, checklowlinkloc, &lowlinkloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, [&instructions, &nodeaddr, &reg0, &lowlinkloc, x]() {
            return reg0 >= ((datavminstruct*)instructions[nodeaddr[x] + lowlinkloc].get())->data; },
            counterloc - checklowlinkloc);
        });
    blueprint.push_back([&reg0, &makenodeaddr, &lowlinkloc](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&reg0]() { return reg0; }, makenodeaddr(x, lowlinkloc));
        });
    blueprint.push_back([&makenodeaddr, &lowlinkloc, &checksccloc](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, [&lowlinkloc, &checksccloc]() {
            return std::make_unique<jcvminstruct>(opcodes::JC, []() { return true; }, lowlinkloc - checksccloc); },
            makenodeaddr(x, checksccloc)); });
    nextedgeloc = blueprint.size();
    blueprint.push_back([counterloc, nextedgeloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, []() { return true; }, counterloc - nextedgeloc); });
    onstackloc = blueprint.size();
    blueprint.push_back([&checksccloc, onstackloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, []() { return true; }, checksccloc - onstackloc); });
    blueprint.push_back([&makenodeaddr, callloc](int x) {
        return std::make_unique<addrvminstruct>(opcodes::PUSH, makenodeaddr(x, callloc + 1)); });
    checksccloc = blueprint.size();
    blueprint.push_back([&lowlinkloc, checksccloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, []() { return false; }, lowlinkloc - checksccloc);
        });
    nextnodeloc = blueprint.size();
    blueprint.push_back([](int x) { return std::make_unique<vminstruct>(opcodes::POP); });
    blueprint.push_back([&reg0, &instructions, starttopo, &nodeaddrsetloc, callloc](int x) {
        return std::make_unique<modinstvminstruct>(opcodes::MODINST, [&reg0, &instructions, starttopo, &nodeaddrsetloc, callloc]() {
            return std::make_unique<addrvminstruct>(opcodes::JMP, [&nodeaddrsetloc, callloc] (size_t reg0) {
                return [&nodeaddrsetloc, callloc, reg0]() {
                    return reg0 + nodeaddrsetloc - (callloc + 1); }; }(reg0)); },
            [&instructions, starttopo]() { return ((datavminstruct*)instructions[starttopo].get())->data; });
        });
    blueprint.push_back([&reg0, &makenodeaddr, nodeaddrloc, &nodeaddrsetloc, callloc](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, makenodeaddr(x, nodeaddrloc),
            [&reg0, &nodeaddrsetloc, callloc]() { return reg0 + nodeaddrsetloc - (callloc + 1); }); });
    blueprint.push_back([&reg0, &nexttopoloc, callloc, starttopo](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&reg0, &nexttopoloc, callloc]() {
            return reg0 + nexttopoloc - (callloc + 1); },
            [starttopo]() { return starttopo; }); });
    blueprint.push_back([&succ, &reg0, nodeaddrloc, callloc](int x) {
        return std::make_unique<storevminstruct>(opcodes::STORE, [&succ]() { return succ.size(); },
            [&reg0, nodeaddrloc, callloc]() { return reg0 + nodeaddrloc - (callloc + 1); }); });
    gotonextnodeloc = blueprint.size();
    blueprint.push_back([&nodeaddr, &reg0, callloc, nextnodeloc, gotonextnodeloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, [&nodeaddr, &reg0, x, callloc]() {
            return nodeaddr[x] + callloc + 1 != reg0; },
            nextnodeloc - gotonextnodeloc); });
    lowlinkloc = blueprint.size();
    blueprint.push_back([](int x) {
        return std::make_unique<datavminstruct>(opcodes::DATA, -1); });
    /*blueprint.push_back([&instructions, &makenodeaddr, &lowlinkloc, nodeaddrloc](int x) {
        return std::make_unique<addrvminstruct>(FUNC, [&instructions, &makenodeaddr, &lowlinkloc, nodeaddrloc, x]() {
            std::cout << x << " " << ((datavminstruct*)instructions[makenodeaddr(x, nodeaddrloc)()].get())->data <<
                " " << ((datavminstruct*)instructions[makenodeaddr(x, lowlinkloc)()].get())->data << std::endl;
            return 0; }); });*/
    retloc = blueprint.size();
    blueprint.push_back([](int x) {
        return std::make_unique<addrvminstruct>(opcodes::JMP, []() { return 0; }); });
    nodeaddrsetloc = blueprint.size();
    blueprint.push_back([](int x) {
        return std::make_unique<datavminstruct>(opcodes::DATA, -1); });
    checksamesccloc = blueprint.size();
    blueprint.push_back([&instructions, &nodeaddr, &reg0, nodeaddrloc, nodeaddrsetloc, &satloc, checksamesccloc](int x) {
        return std::make_unique<jcvminstruct>(opcodes::JC, [&instructions, &nodeaddr, &reg0, nodeaddrloc, nodeaddrsetloc, x]() { return
            reg0 != ((datavminstruct*)instructions[nodeaddr[-x]+nodeaddrsetloc].get())->data; },
            satloc - checksamesccloc);
        });
    blueprint.push_back([UNSAT](int x) {
        return std::make_unique<addrvminstruct>(opcodes::JMP, [UNSAT]() { return UNSAT; }); });
    satloc = blueprint.size();
    blueprint.push_back([&sol](int x) {
        return std::make_unique<addrvminstruct>(opcodes::FUNC, [&sol, x]() {
            if (sol.find(-x) == sol.end()) sol.insert(x); return 0; });
        });    
    nexttopoloc = blueprint.size();
    blueprint.push_back([SAT](int x) {
        return std::make_unique<addrvminstruct>(opcodes::JMP, [SAT]() { return SAT; }); });
    std::for_each(succ.begin(), succ.end(), [&nodeaddr, &instructions, &blueprint]
    (std::pair<int, std::vector<int>> p) {
            int x = p.first;
            nodeaddr[x] = instructions.size();
            std::vector<std::unique_ptr<vminstruct>> builtblueprint;
            std::transform(blueprint.begin(), blueprint.end(), std::back_inserter(builtblueprint),
                [x](std::function<std::unique_ptr<vminstruct>(int)> f) { return f(x); });
            //instructions.insert(instructions.end(), builtblueprint.begin(), builtblueprint.end());
            std::move(builtblueprint.begin(), builtblueprint.end(), std::back_inserter(instructions));
        });
    size_t instptr = 0;
    while (instptr != SAT && instptr != UNSAT) {
        //std::cout << instptr << " " << opstrs[instructions[instptr]->opcode] << " " << reg0 << " " << s.size() << " " << (s.empty() ? -1 : s.top()) << std::endl;
        switch (instructions[instptr]->opcode) {
        case opcodes::CALL:
            s.push(instptr + 1);
            instptr = ((addrvminstruct*)instructions[instptr].get())->address();
            break;
        case opcodes::DATA:
            reg0 = ((datavminstruct*)instructions[instptr].get())->data; instptr++;
            break;
        case opcodes::JMP:
            instptr = ((addrvminstruct*)instructions[instptr].get())->address();
            break;
        case opcodes::LOAD:
            reg0 = ((datavminstruct*)instructions[((datavminstruct*)instructions[instptr].get())->data].get())->data;
            instptr++;
            break;
        case opcodes::STORE:
        {
            size_t addr = ((storevminstruct*)instructions[instptr].get())->address();
            assert(instructions[addr]->opcode == opcodes::DATA);
            ((datavminstruct*)instructions[
                addr].get())->data =
                ((storevminstruct*)instructions[instptr].get())->data();
                instptr++;
                break;
        }
        case opcodes::POP:
            reg0 = s.top(); s.pop(); instptr++; break;
        case opcodes::MODINST:
            instructions[
                ((modinstvminstruct*)instructions[instptr].get())->address()] =
                ((modinstvminstruct*)instructions[instptr].get())->data();
            instptr++;
            break;
        case opcodes::JC:
            if (((jcvminstruct*)instructions[instptr].get())->cond())
                instptr += ((jcvminstruct*)instructions[instptr].get())->offset;
            else instptr++;
            break;
        case opcodes::RET:
            instptr = s.top(); s.pop(); break;
        case opcodes::PEEK:
            reg0 = s.top(); instptr++; break;
        case opcodes::NOP:
            instptr++; break;
        case opcodes::FUNC:
            ((addrvminstruct*)instructions[instptr].get())->address();
            instptr++; break;
        case opcodes::PUSH:
            s.push(((addrvminstruct*)instructions[instptr].get())->address());
            instptr++; break;
        default:
            assert(false);
        }
    }
    assert(s.size() == 0);
    std::vector<int> solv;
    if (instptr == UNSAT) return solv;
    solv.insert(solv.begin(), sol.begin(), sol.end());
    std::sort(solv.begin(), solv.end(), [](int x, int y) { return abs(x) < abs(y); });
    return solv;
}
#endif

void performanceMeasure(std::function<void()> f, int numTimes)
{
    auto start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < numTimes; i++) f();
    auto finish = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = finish - start;
    std::cout << "Elapsed time: " << elapsed.count() / numTimes << "s\n";
}

extern void test_irreducible();

//https://codegolf.stackexchange.com/questions/1933/solve-2-sat-boolean-satisfiability
int main()
{
    test_irreducible();
#if defined(_M_X64) || defined(__amd64__)
    //parseasmlisting("x64\\debug\\selfmodmodel.lst"); return 0;
#else
    //parseasmlisting("debug\\selfmodmodel.lst"); return 0;
#endif
    std::vector<std::pair<int, int>> testformula1 = { {1, 2}, {-1, 2}, {-2, 1}, {-1, -2} }; //no solutions
    std::vector<std::pair<int, int>> testformula2 = { {1, 2}, {2, 3}, {3, 4}, {-1, -3}, {-2, -4} }; //1 unique solution
    std::vector<std::pair<int, int>> testformula3 = { //3 solutions
        {1, 4}, {-2, 5}, {3, 7}, {2, -5}, {-8, -2}, {3, -1}, {4, -3}, {5, -4}, {-3, -7}, {6, 7}, {1, 7}, {-7, -1} }; 
    std::vector<std::pair<int, int>> testformula4 = { {21, 34}, {-49, -12}, {7, 18}, {-5, -1}, {28, 17}, {3, 55}, {36, 33}, {-6, -50}, {44, -41}, {-55, 3}, {14, -54}, {-30, 13}, {-13, 60}, {54, -16}, {-48, 41}, {3, 6}, {49, -48}, {34, -4}, {14, -46}, {58, -20}, {52, 54}, {-37, -25}, {56, -1}, {50, -9}, {-58, 11}, {-19, 58}, {17, 8}, {56, 51}, {38, 49}, {-13, 36}, {24, 9}, {18, -29}, {6, 49}, {-30, 4}, {-13, -20}, {31, -9}, {54, -4}, {37, 17}, {-48, -8}, {-7, -45}, {-3, -42}, {27, -22}, {-50, -27}, {47, 19}, {-21, 20}, {-20, -37}, {-42, 12}, {-35, 1}, {-41, -19}, {11, 30}, {-17, -48}, {21, -49}, {16, -53}, {57, 57}, {15, 2}, {-6, -7}, {-23, -28}, {-12, -17}, {-59, -36}, {38, -6}, {-16, -6}, {21, -14}, {17, -7}, {3, -49}, {-55, -13}, {22, -52}, {24, -56}, {22, -42}, {13, -4}, {-8, -16}, {-55, -7}, {-12, 48}, {52, 18}, {-47, 44}, {-22, -23}, {-29, -23}, {-53, 57}, {-38, 54}, {43, -53}, {49, -18}, {-60, 58}, {-5, -14}, {16, 34}, {-24, -43}, {10, -21}, {-52, -40}, {-45, -22}, {-5, -11}, {-32, -11}, {-15, 11}, {-24, 44}, {-17, -15}, {10, -27}, {8, -26}, {-36, 24}, {13, 1}, {59, -34}, {-40, -25}, {11, -22} }; //many solutions
    std::vector<std::vector<std::pair<int, int>>> testformulae = { testformula1, testformula2, testformula3, testformula4 };
    std::for_each(testformulae.begin(), testformulae.end(), [](std::vector<std::pair<int, int>> testformula) {
        //std::map<int, std::vector<int>> succ = gettwosatgraph(testformula1);
        //tarjan_scc(succ);
        //printtwosat(twosat(testformula));
        performanceMeasure([&testformula]() { alltwosat(testformula, false, twosat, 1000); }, 10);
#ifdef USE_VM
        performanceMeasure([&testformula]() { alltwosat(testformula, false, selfmodvmtwosat, 1000); }, 10);
#endif
        performanceMeasure([&testformula]() { alltwosat(testformula, false, selfmodtwosatasm, 1000); }, 10);
        });
}