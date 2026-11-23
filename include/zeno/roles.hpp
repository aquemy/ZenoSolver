#pragma once

#include <zeno/instance.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/plan.hpp>
#include <zeno/reduce.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

namespace zeno
{
/// Packed state key of BalancedRoles (a GCC/Clang extension; __extension__
/// keeps -Wpedantic quiet).
__extension__ typedef unsigned __int128 RoleKey;

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
    std::vector<std::vector<RoleKey>> keys_; ///< per layer: packed (imbalance, landings)
    std::vector<std::vector<Entry>> layers_;
    bool complete_ = true;
    Cost value_ = kInfCost;
    std::size_t final_ = 0;
};

/// Role relaxation at level T (under A1-NS, Theorem 6.1): every plane flies
/// an odd number >= 1 of crossings (weight fill) and its other landings weigh
/// at least min(drop, pick); and as drop-offs and pick-ups pair up city by
/// city, all planes' loads add up to fill(X), so the largest is at least
/// fill(X) / p. bound(T) is the larger of the two bounds; oddGroup(m, T) is the
/// per-plane bound of a plane with m landings.
class RoleRelaxation
{
public:
    RoleRelaxation(const ReducedInstance& r, Time maxLevel);
    [[nodiscard]] Cost bound(Time T) const;
    [[nodiscard]] Cost oddGroup(int m, Time T) const;
    [[nodiscard]] Time maxLevel() const noexcept { return maxLevel_; }

private:
    struct Stair
    {
        Time load = 0;
        Cost cost = 0;
    };
    const ReducedInstance& r_;
    Time maxLevel_;
    std::vector<std::array<std::vector<Stair>, 2>> stairs_; ///< per m and crossing parity
    OnePlaneTable total_;                                    ///< s landings, fill weights, level p * T
};

/// remaining[q][j]: a lower bound (the role relaxation per plane) on q more
/// planes carrying j more landings at level T, for BalancedRoles' pruning.
[[nodiscard]] std::vector<std::vector<Cost>> remainingPlanesBound(const ReducedInstance& r, const RoleRelaxation& roles, Time T);

/// The Lagrangian bound for given multipliers: a drop-off in city i costs
/// c_i + mu_i, a pick-up c_i - mu_i; the balance constraint drops out (the
/// mu terms cancel on balanced configurations), and the planes decouple into
/// knapsacks with an odd number of crossings. A lower bound on the cheapest
/// balanced role configuration at level T for every mu (under A1-NS).
/// kInfCost when no configuration fits; std::numeric_limits<Cost>::min()
/// when the dense knapsack would exceed `cellLimit` cells.
[[nodiscard]] Cost lagrangianValue(const ReducedInstance& r, Time T, const std::vector<Cost>& mu,
                                   std::size_t cellLimit = std::size_t{1} << 24);

struct LagrangianBound
{
    Cost value = 0;
    std::vector<Cost> multipliers; ///< mu with lagrangianValue(r, T, mu) == value
};

/// Subgradient search for multipliers that raise the Lagrangian bound to
/// `target`, for up to `iterations` rounds, stopping as soon as it reaches it.
/// Multipliers stay within [-(s max c + 1), s max c + 1].
[[nodiscard]] LagrangianBound lagrangianRoles(const ReducedInstance& r, Time T, Cost target, int iterations = 60,
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
