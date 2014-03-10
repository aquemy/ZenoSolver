#ifndef _ZS_UTILS_
#define _ZS_UTILS_
 
#include <functional>
#include <map>

////////////////////////////////////////////////////////////
/// \brief Print a message and execute a void(void) function.
///
/// \param title Title to be printed.
/// \param f Function to be called.
////////////////////////////////////////////////////////////
void debugPrint(std::string title, std::function<void(void)> f);

////////////////////////////////////////////////////////////
/// \brief Test if a file is readable.
///
/// \param path Path to the file.
///
/// \return True if the file is readable, false otherwise.
////////////////////////////////////////////////////////////
bool isReadable(const std::string& path);

////////////////////////////////////////////////////////////
/// \brief Generate a PDDL file according to the instance.
///
/// TODO: Parameter to modify the name of the domain.
///
/// \param path Path where to generate the file.
/// \param n Number of cities.
/// \param t Number of travelers.
/// \param p Number of planes.
/// \param c Vector of cost / risk.
/// \param d Vector of durations.
/// \param pareto Map containing the Pareto Front.
////////////////////////////////////////////////////////////
void generatePDDL(std::string path, unsigned n, unsigned t, unsigned p, 
    const std::vector<double>& c, 
    const std::vector<double>& d, 
    const std::map<int,int>& pareto = std::map<int,int>());

#endif // _ZS_UTILS_


