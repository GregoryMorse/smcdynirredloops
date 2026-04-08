#include <functional>
#include <iostream>

//https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.35.8991&rep=rep1&type=pdf
#define EXIT 0
#define LOOP 1
#define FORWARD 2

typedef void(*irred_loop_type)(bool u_start,
    std::function<int()> w_cond, std::function<int()> x_cond,
    std::function<void()> u, std::function<void()> v,
    std::function<void()> w, std::function<void()> x);

void irreducible_loops_no_goto(bool u_start,
    std::function<int()> w_cond, std::function<int()> x_cond,
    std::function<void()> u, std::function<void()> v,
    std::function<void()> w, std::function<void()> x)
{
    bool is_end = false, v_first = !u_start;
    do {
        if (!v_first) u();
        do {
            if (!v_first) {
                w();
                bool loop = false;
                switch (w_cond()) {
                case EXIT: is_end = true;
                case LOOP: loop = true;
                }
                if (loop) break;
            }
            do {
                if (!v_first) {
                    x();
                    bool loop = false;
                    switch (x_cond()) {
                    case EXIT: is_end = true;
                    case LOOP: loop = true;
                    }
                    if (loop) break;
                }
                v();
                v_first = false;
            } while (true);
        } while (!is_end);
    } while (!is_end);
}

void irreducible_loops(bool u_start,
       std::function<int()> w_cond, std::function<int()> x_cond,
       std::function<void()> u, std::function<void()> v,
       std::function<void()> w, std::function<void()> x)
{
    bool loop;
    if (!u_start) goto do_v;
    do {
        u();
        do {
            w();
            loop = false;
            switch (w_cond()) {
            case EXIT: goto end;
            case LOOP: loop = true;
            }
            if (loop) break;
            do {
                x();
                loop = false;
                switch (x_cond()) {
                case EXIT: goto end;
                case LOOP: loop = true;
                }
                if (loop) break;
do_v:
                v();
            } while (true);
        } while (true);
    } while (true);
end:
    return;
}

void irreducible_loops_only_goto(bool u_start,
    std::function<int()> w_cond, std::function<int()> x_cond,
    std::function<void()> u, std::function<void()> v,
    std::function<void()> w, std::function<void()> x)
{
    if (!u_start) goto do_v;
do_u:
    u();
do_w:
    w();
    switch (w_cond()) {
    case EXIT: goto end;
    case LOOP: goto do_u;
    }
do_x:
    x();
    switch (x_cond()) {
    case EXIT: goto end;
    case LOOP: goto do_w;
    }
do_v:
    v();
    goto do_x;
end:
    return;
}

void test_irreducible()
{
    irred_loop_type ilt[] = { irreducible_loops_no_goto,
        irreducible_loops, irreducible_loops_only_goto };
    for (int i = 0; i < 3; i++) {
        int u = 0, v = 0, w = 0, x = 0;
        srand(1);
        ilt[i](rand() & 1, []() { return rand() % 3; },
            []() { return rand() % 3; }, [&u]() { u++; },
            [&v]() { v++; }, [&w]() { w++; }, [&x]() { x++; });
        std::cout << u << " " << v << " " << w << " " << x << std::endl;
    }
}
