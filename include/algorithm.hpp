#ifndef _ZS_ALGORITHM_
#define _ZS_ALGORITHM_

#include <set>

constexpr const bool EAST = true;
constexpr const bool WEST = false;

////////////////////////////////////////////////////////////
/// \brief Handle duration and direction of a plane.
///
////////////////////////////////////////////////////////////
struct Si
{
    double m = 0;       ///< Current duration for plane i.
    bool   s = EAST;    ///< Indicates next flight direction.
};

////////////////////////////////////////////////////////////
/// \brief Comparator using makespan.
///
/// \param i First plane.
/// \param j Second plane.
///
/// \return True i greater than j according to makespan.
////////////////////////////////////////////////////////////
bool compM(const Si i, const Si j);

////////////////////////////////////////////////////////////
/// \brief Comparator using makespan and direction.
///
/// This comparator consider that a plane that has to flight
/// to the east is always greater than a plane that has to
/// flight to the west, and vice versa.
/// If both will fly to the east, we take into consideration
/// the makespan.
///
/// \param i First plane.
/// \param j Second plane.
///
/// \return True i greater than j.
////////////////////////////////////////////////////////////
bool compMS(Si& i, Si& j);

////////////////////////////////////////////////////////////
/// \brief Compute the optimal makespan for a given PPP.
///
/// This function call either the algorithm for a symetric
/// problem or non-symetric problems. More details and 
/// proofs of optimality can be found in doc/zenobench.pdf.
///
/// \param Mc Current makespan or upper bound).
/// \param Ml Lower bound.
/// \param e Eastbound cities.
/// \param w Westbound cities.
/// \param betaPowerSet Powerset according to patterns 3.
/// \param d Vector of west durations
/// \param de Vector of east durations.
/// \param p Number of planes.
/// \param symetric True if the problem is symetric
///
/// \return Optimal makespan.
////////////////////////////////////////////////////////////
int UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p,
    bool symetric);

////////////////////////////////////////////////////////////
/// \brief Symetric version of the algorithm.
///
/// \param Mc Current makespan or upper bound).
/// \param Ml Lower bound.
/// \param e Eastbound cities.
/// \param w Westbound cities.
/// \param betaPowerSet Powerset according to patterns 3.
/// \param d Vector of west durations
/// \param de Vector of east durations.
/// \param p Number of planes.
///
/// \return Optimal makespan.
////////////////////////////////////////////////////////////
int UpperBound_Symetric(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p);

////////////////////////////////////////////////////////////
/// \brief Non-symetric version of the algorithm.
///
/// \param Mc Current makespan or upper bound).
/// \param Ml Lower bound.
/// \param e Eastbound cities.
/// \param w Westbound cities.
/// \param betaPowerSet Powerset according to patterns 3.
/// \param d Vector of west durations
/// \param de Vector of east durations.
/// \param p Number of planes.
///
/// \return Optimal makespan.
////////////////////////////////////////////////////////////
int UpperBound_NonSymetric(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p);

#endif // _ZS_ALGORITHM_
