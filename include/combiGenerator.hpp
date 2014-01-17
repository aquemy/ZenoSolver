#ifndef _ZS_COMBI_GENERATOR_
#define _ZS_COMBI_GENERATOR_

#define GEN_NEXT  0 //ok, print and continue
#define GEN_TERM  1 //ok, terminate
#define GEN_EMPTY 2 //ok, print EMPTY SET and continue
#define GEN_ERROR 3 //an error occured, print an error message and terminate

int nextTuple(std::vector<int>& vec, const int n, const int k);

std::vector<std::vector<int>> generateTuples(const int n, const int k, bool serialize = false);

std::vector<std::vector<int>> readTuples(const int n, const int k);

#endif // _ZS_COMBI_GENERATOR_
