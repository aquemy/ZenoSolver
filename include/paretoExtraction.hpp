#ifndef _ZS_PARETO_EXTRACTION_
#define _ZS_PARETO_EXTRACTION_

#include <algorithm.hpp>

////////////////////////////////////////////////////////////
/// \brief Extract the Pareto Front from a std::map.
///
/// The algorithm is in $O(n)$ where n is the size of the map.
/// The counter part is the logarithmic insertion. Howerver,
/// the process can be improved using **hint** and then, be
/// in to $O(1)$.
///
/// \param front Points to be extracted.
///
/// \return std::map containing the Pareto Front.
////////////////////////////////////////////////////////////
std::map<int, int> paretoExtraction(std::map<int, int>& front);

std::map<int, Plan> paretoExtractionPlan(std::map<int, Plan>& front);

#endif // _ZS_GEN_FUNCTION_
