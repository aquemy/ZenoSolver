#pragma once

#include <zeno/instance.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/plan.hpp>
#include <zeno/reduce.hpp>

#include <cstddef>
#include <optional>
#include <vector>

namespace zeno
{
/// A role configuration (theory note, section 6): per plane, the cities of
/// its drop-offs (C_I -> x -> C_I, weight 2 d_x), pick-ups (C_G -> x -> C_G,
/// weight 2 dbar_x) and crossings (an odd number, weight d_x + dbar_x), in
/// reduced city indices. Drop-offs and pick-ups balance city by city.
struct RoleConfig
{
    std::vector<std::vector<int>> drops, picks, crossings;
};

/// Cheapest balanced role configuration of s landings whose planes all have
/// load <= T (level units), by a DP over planes on the imbalance vector
/// (drop-offs minus pick-ups so far, per city).
///
/// A plane needs no city where it both drops off and picks up: such a pair
/// weighs and costs exactly two crossings in that city, so a plane is its
/// imbalance Delta (drop-offs Delta+, pick-ups Delta-) plus an odd number of
/// crossings. ||Delta||_1 <= t - p because a configuration has at most t - p
/// links. Under assumption A1-NS every plan is weakly dominated by a role
/// configuration with the same cost and a load bound equal to its makespan
/// (Theorem 6.1), so the value is a lower bound on the cost of every plan of
/// makespan <= makespanPerLevel * T.
///
/// The state space grows like (2n)^(t-p); the program gives up (complete()
/// is false) beyond `stateLimit` states or `workLimit` transitions.
class BalancedRoles
{
public:
    /// With a finite `target`, the search only looks for configurations
    /// cheaper than it: a state is pruned when its cost plus
    /// remaining[q][j] (a lower bound on q more planes with j more landings)
    /// reaches the target. value() is then the optimum if it is below the
    /// target, and the target itself otherwise (a lower bound).
    BalancedRoles(const ReducedInstance& r, const OnePlaneTable& fill, Time T, std::size_t stateLimit = 2'000'000,
                  std::size_t workLimit = 50'000'000, Cost target = kInfCost,
                  const std::vector<std::vector<Cost>>* remaining = nullptr);

    [[nodiscard]] bool complete() const noexcept { return complete_; }
    [[nodiscard]] Cost value() const noexcept { return value_; }
    /// True when the value is an optimum (below the target), not just the target.
    [[nodiscard]] bool optimal() const noexcept { return complete_ && value_ < target_; }
    /// An optimal configuration. Requires complete() and a finite value.
    [[nodiscard]] RoleConfig reconstruct() const;

private:
    struct Option
    {
        std::vector<int> delta; ///< per city
        Time load = 0;
        Cost cost = 0;
        int landings = 0;
    };
    struct Entry
    {
        Cost cost;
        int option, crossings; ///< last plane: option index and number of crossings
        std::size_t parent;    ///< state index in the previous layer
    };

    const ReducedInstance& r_;
    const OnePlaneTable& fill_;
    Time T_;
    Cost target_;
    std::vector<Option> options_;
    std::vector<std::vector<std::pair<std::vector<int>, int>>> keys_; ///< per layer: (imbalance, landings)
    std::vector<std::vector<Entry>> layers_;
    bool complete_ = true;
    Cost value_ = kInfCost;
    std::size_t final_ = 0;
};

/// Lagrangian lower bound on the cheapest balanced role configuration at
/// level T: with an integer multiplier mu_i per city, a drop-off in i costs
/// c_i + mu_i and a pick-up c_i - mu_i, so the balance constraint drops out
/// (the mu terms cancel on balanced configurations) and the planes decouple
/// into knapsacks with an odd number of crossings. Every mu gives a lower
/// bound (under A1-NS, like BalancedRoles); mu follows subgradient steps
/// towards `target` for up to `iterations` rounds, stopping as soon as the
/// bound reaches it. Returns the best bound found, or -infinity (as 0 or
/// below) when the dense knapsack would exceed `cellLimit` cells.
[[nodiscard]] Cost lagrangianRoles(const ReducedInstance& r, Time T, Cost target, int iterations = 60,
                                   std::size_t cellLimit = std::size_t{1} << 24);

/// A schedule of a role configuration: drop-offs first, crossings, pick-ups
/// last (the template lemma N3), so drop-offs never wait and a pick-up waits
/// at most for its passenger. Starts from pick-ups sorted by the time their
/// passenger is dropped, then improves the makespan by local search (swaps of
/// two drop-offs or two pick-ups of a plane, exchange of the passengers of two
/// pick-ups in the same city), up to `budget` evaluations. It is a heuristic:
/// the plan is real (checked by simulation) but not always the best schedule.
/// Returns nothing if the configuration cannot carry the t passengers.
[[nodiscard]] std::optional<Plan> scheduleRoles(const Instance& instance, const ReducedInstance& r, const RoleConfig& config,
                                                std::size_t budget = 20000);
} // namespace zeno
