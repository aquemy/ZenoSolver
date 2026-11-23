#ifndef _ZS_CLI_
#define _ZS_CLI_

#include <string>
#include <vector>

#include <tclap/CmdLine.h>

////////////////////////////////////////////////////////////
/// \brief Command-line arguments shared by every solver
/// variant and by the brute-force test oracle.
///
/// The arguments register themselves on \p cmd at
/// construction, so this object must outlive cmd.parse().
////////////////////////////////////////////////////////////
struct CliArgs
{
    explicit CliArgs(TCLAP::CmdLine& cmd);

    TCLAP::ValueArg<int> nArg;
    TCLAP::ValueArg<int> tArg;
    TCLAP::ValueArg<int> pArg;
    TCLAP::ValueArg<int> rArg;
    TCLAP::ValueArg<std::string> dArg;
    TCLAP::SwitchArg aArg;
    TCLAP::SwitchArg GArg;
    TCLAP::SwitchArg SArg;
    TCLAP::ValueArg<unsigned> BArg;
    TCLAP::ValueArg<unsigned> CArg;
    TCLAP::ValueArg<unsigned> DArg;
    TCLAP::ValueArg<unsigned> DEArg;
    TCLAP::ValueArg<unsigned> DWArg;
    TCLAP::ValueArg<double> ScArg;
    TCLAP::ValueArg<double> TcArg;
    TCLAP::ValueArg<double> SdArg;
    TCLAP::ValueArg<double> TdArg;
    TCLAP::ValueArg<double> xArg;
    TCLAP::ValueArg<double> yArg;
    TCLAP::SwitchArg genPlan;
    TCLAP::SwitchArg FArg;
    TCLAP::ValueArg<std::string> OArg;
};

////////////////////////////////////////////////////////////
/// \brief Instance data, after generation or loading,
/// integer conversion and normalisation.
////////////////////////////////////////////////////////////
struct InstanceData
{
    unsigned n = 0;              ///< Number of central cities.
    unsigned t = 0;              ///< Number of travelers.
    unsigned p = 0;              ///< Number of planes.
    std::vector<double> c;       ///< Landing cost per city.
    std::vector<double> d;       ///< West durations (c_I <-> c_i).
    std::vector<double> de;      ///< East durations (c_i <-> c_G).
    bool symetric = false;       ///< True if d == de by construction.
};

////////////////////////////////////////////////////////////
/// \brief Validate the arguments and build the instance.
///
/// Throws std::domain_error or std::runtime_error on
/// invalid input.
////////////////////////////////////////////////////////////
InstanceData buildInstance(CliArgs& args);

#endif // _ZS_CLI_
