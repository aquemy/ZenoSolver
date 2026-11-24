#pragma once

#include <zeno/instance.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/plan.hpp>
#include <zeno/reduce.hpp>
#include <zeno/roles.hpp>

#include <chrono>
#include <cstddef>
#include <optional>
#include <utility>
#include <vector>

namespace zeno
{
/// A template schedule (Lemma 6.3 of the theory note): per plane, its
/// drop-offs in order, its crossings, its pick-ups in order, and for pick-up l
/// of plane k the drop-off (plane, position) whose passenger it collects.
struct TemplateSchedule
{
    std::vector<std::vector<int>> drops, picks, crossings; ///< reduced city indices
    std::vector<std::vector<std::pair<std::size_t, std::size_t>>> match;
};

/// Makespan of the template (original time units): drop-offs from time 0,
/// then the crossings, then the pick-ups, each waiting for its passenger.
[[nodiscard]] Time templateMakespan(const Instance& instance, const ReducedInstance& r, const TemplateSchedule& schedule);
/// The template as a plan (checked by checkPlan in the tests).
[[nodiscard]] Plan templatePlan(const Instance& instance, const ReducedInstance& r, const TemplateSchedule& schedule);

using Deadline = std::chrono::steady_clock::time_point;

struct ExactSchedule
{
    bool complete = true;                   ///< false when the budget ran out
    std::optional<TemplateSchedule> best;   ///< a schedule with makespan < below, if one exists
    Time makespan = 0;                      ///< its makespan
};

/// Searches the schedules of a role configuration for one with makespan
/// strictly below `below` (original units): every order of the drop-offs on
/// each plane and every matching of drop-offs to pick-ups in each city (no
/// plane collects its own passenger), the pick-ups of each plane in order of
/// release (passenger available minus the flight to the city), which is
/// optimal for fixed drop-offs and matching. By Lemma 6.3 the template is
/// optimal for fixed orders and matching, so with `complete` the absence of
/// a result proves that the configuration's least makespan is >= below.
/// Gives up (complete = false) after `budget` steps or at `deadline`.
[[nodiscard]] ExactSchedule exactSchedule(const Instance& instance, const ReducedInstance& r, const RoleConfig& config, Time below,
                                          std::size_t budget = 2'000'000, Deadline deadline = Deadline::max());

struct GapSearch
{
    enum class Outcome
    {
        Closed,     ///< no role configuration of cost < costBelow has a schedule finishing before makespanBelow
        Found,      ///< `found` is such a configuration's plan
        Incomplete, ///< the budget ran out
    };
    Outcome outcome = Outcome::Incomplete;
    std::optional<std::pair<FrontPoint, Plan>> found;
    std::size_t configurations = 0; ///< configurations scheduled
};

/// Exact search of a gap of the non-symmetric bracket (Corollary 6.10): every
/// role configuration of cost < costBelow whose plane loads fit in level T,
/// each with exactSchedule against makespanBelow. Planes are enumerated in a
/// canonical order (as a multiset of plane contents), crossings only at the
/// Pareto points of the crossing table (cheaper and shorter crossings never
/// hurt a template), pruned with the role relaxation on the remaining planes.
/// Closed is a proof under (A1-NS) for every feasible plan, also when a city
/// has d = dbar = 0 (Theorem 6.9; Corollary 6.10).
/// Stops (Incomplete) after `budget` steps or at `deadline`.
[[nodiscard]] GapSearch searchGap(const Instance& instance, const ReducedInstance& r, const OnePlaneTable& fill, const RoleRelaxation& roles,
                                  Time T, Cost costBelow, Time makespanBelow, std::size_t budget = 20'000'000,
                                  Deadline deadline = Deadline::max());
} // namespace zeno
