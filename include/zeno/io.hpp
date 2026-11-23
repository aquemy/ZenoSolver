#pragma once

#include <zeno/instance.hpp>
#include <zeno/legacy_input.hpp>

#include <iosfwd>
#include <string>
#include <vector>

namespace zeno
{
/// PDDL problem for the domain pddl/multi-zeno-travel.pddl. city0 is C_I,
/// city1..cityN the central cities, city(N+1) is C_G; every person and every
/// plane starts in C_I and must end in C_G. Flights C_I <-> i last d_i,
/// C_G <-> i last dbar_i, and i <-> j last max(d_i, dbar_i) + max(d_j,
/// dbar_j) + 100, which is never faster than through a hub (assumption A1).
/// When `front` is given, it is appended as "; makespan cost" comments.
void writePddlProblem(std::ostream& out, const Instance& instance, const Front* front = nullptr);

/// "zeno<n>n<t>t<p>pMulti.pddl", the 2016 default name.
[[nodiscard]] std::string defaultPddlName(const Instance& instance);

/// Data file read by -d: durations then costs (symmetric), or C_I-side
/// durations, C_G-side durations, costs.
void writeDataFile(std::ostream& out, const Instance& instance);

namespace cli
{
/// Instance options of the command line (2016 syntax), parsed out of `args`.
struct InstanceArguments
{
    legacy::Options options;
    std::vector<std::string> rest; ///< tokens that are not instance options, in order
};

/// Consumes -n -t -p -d -C -D -E -W -r -j -k -l -m -x -y and their values,
/// and drops -F (kept for compatibility). Throws std::invalid_argument on a
/// missing or malformed value.
[[nodiscard]] InstanceArguments parseInstanceArguments(const std::vector<std::string>& args);

/// Help text for those options.
[[nodiscard]] const char* instanceOptionsHelp();

/// Parses an integer option value; throws std::invalid_argument.
[[nodiscard]] int integerValue(const std::string& flag, const std::string& value);
} // namespace cli
} // namespace zeno
