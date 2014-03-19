#ifndef _ZS_GEN_FUNCTION_
#define _ZS_GEN_FUNCTION_

////////////////////////////////////////////////////////////
/// \brief Apply a transformation to a vector.
///
/// Apply a transformation such that $v(i) = x*f(a*i + b) + y$.
///
/// \param v The vector to be modified.
/// \param f The function to be applied.
/// \param x Scale factor.
/// \param y Translation factor.
/// \param a Scale factor for argument.
/// \param b Translation factor for argument.
////////////////////////////////////////////////////////////
void apply(std::vector<double>& v, std::function<double(unsigned)> f, double x = 1, double y = 0, double a = 1, double b = 0);

////////////////////////////////////////////////////////////
/// \brief Apply a backward transformation to a vector.
///
/// Apply a transformation such that $v(i) = x*f(a*(n - i) + b) + y$.
/// Where n is the size of the vector v.
///
/// \param v The vector to be modified.
/// \param f The function to be applied.
/// \param x Scale factor.
/// \param y Translation factor.
/// \param a Argument scale factor.
/// \param b Argument translation factor.
////////////////////////////////////////////////////////////
void rapply(std::vector<double>& v, std::function<double(unsigned)> f, double x = 1, double y = 0, double a = 1, double b = 0);

double f1(unsigned i);
double f2(unsigned i);
double f3(unsigned i);
double f4(unsigned i);
double f5(unsigned i);

#endif // _ZS_GEN_FUNCTION_
