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

////////////////////////////////////////////////////////////
/// \brief Compute the next k-partition.
///
/// Compute the k-partitions according to Knuth,
/// Donald E.: The Art of Computer Programming.
///
/// \param vec Vector to receive the tuple.
/// \param t
/// \param n
///
/// \return NEXT if it exists another tuple, DONE otherwise.
////////////////////////////////////////////////////////////
int nextkPartition(std::vector<int>& vec, unsigned int t, unsigned int n);

////////////////////////////////////////////////////////////
/// \brief Greedily compute the largest combinaison.
///
/// Compute the largest partition of S into t with 
/// a maximal value of n per partition element.
///
/// \param S Sum to partition.
/// \param n Maximal value per partition element.
/// \param t Number of partitions.
/// \param e Vector to receive the combinaison.
///
/// \return NEXT if it exists another tuple, DONE otherwise.
////////////////////////////////////////////////////////////
int generateLargestCombi(int S, int n, int t, std::vector<int>& e);

#endif // _ZS_COMBI_GENERATOR_
