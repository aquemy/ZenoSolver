#ifndef _ZS_COMBI_GENERATOR_
#define _ZS_COMBI_GENERATOR_

constexpr const int NEXT = 0;
constexpr const int DONE = 1;

////////////////////////////////////////////////////////////
/// \brief Compute the next tuple.
///
/// Compute tuple as a combinaison according to Knuth,
/// Donald E.: The Art of Computer Programming.
///
/// \param vec Vector to receive the tuple.
/// \param n
/// \param k
///
/// \return NEXT if it exists another tuple, DONE otherwise.
////////////////////////////////////////////////////////////
int nextTuple(std::vector<int>& vec, const int n, const int k);

#endif // _ZS_COMBI_GENERATOR_
