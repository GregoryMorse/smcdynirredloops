// Figure 2(a) check (plan R8 item 3): prints the output of the product's parseasmlisting for a listing file.
#define main product_main
#include "../../native/selfmodgraph.cpp"
#undef main
int main(int argc, char** argv)
{
    if (argc < 2) return 2;
    parseasmlisting(argv[1]);
    return 0;
}
void test_irreducible() {}
