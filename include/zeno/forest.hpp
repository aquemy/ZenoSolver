#pragma once

#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>

#include <cstdint>
#include <vector>

namespace zeno
{
/// Work counters of the level evaluations (summed over calls).
struct LevelStats
{
    std::uint64_t states = 0;      ///< DP cells written
    std::uint64_t relaxations = 0; ///< candidate transitions examined
};

/// One plane of a link forest. Its group is X = filler + {parentCity} (when
/// it has a parent) + one landing in the city of each child edge. In the plan
/// of Theorem 4.1 the parent drops a passenger in parentCity and this plane
/// picks it up, so every plane picks up at most once.
struct ForestPlane
{
    std::vector<int> filler; ///< odd number of landings (reduced city indices)
    int parent = -1;         ///< plane index, -1 for a root
    int parentCity = -1;     ///< label of the edge to the parent
};

/// p planes; their groups form an admissible partition of the landings.
struct LinkForest
{
    std::vector<ForestPlane> planes;

    /// Group of plane k (reduced city indices).
    [[nodiscard]] std::vector<int> group(std::size_t k) const;
    /// Children of plane k.
    [[nodiscard]] std::vector<std::size_t> children(std::size_t k) const;
};

/// The value functions of a level T (half makespan): the cheapest partition of
/// the s = 2t - p landings into p non-empty groups whose durations each sum to
/// at most T, +infinity when none exists. G must cover the level T and at
/// least maxGroup() landings.
///
/// relaxedCost has no admissibility constraint: a lower bound on E(T) for
/// every symmetric instance, central flights included (lemma R).
[[nodiscard]] Cost relaxedCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, LevelStats* stats = nullptr);

/// Admissible partitions given by a link forest whose trees have at most
/// `maxTreePlanes` planes. A plane u holds an odd filler plus one landing per
/// incident edge, an edge labelled a putting a landing in a at both ends, so
/// |X_u| - deg(u) is odd and the partition is admissible: the value is an
/// upper bound on E(T), and E(T) itself once maxTreePlanes >=
/// ReducedInstance::maxTree() (link-forest lemma). maxTreePlanes = 2 gives
/// the pairs bound U, 3 the bound U3.
///
/// The children of a plane are kept as Pareto staircases over (tau, cost),
/// tau being the part of the plane's load taken by its child edges, so the
/// work depends on the staircase sizes and not on the magnitude of T.
class ForestProgram
{
public:
    ForestProgram(const ReducedInstance& r, const OnePlaneTable& G, Time T, int maxTreePlanes, LevelStats* stats = nullptr);

    [[nodiscard]] Cost value() const noexcept { return value_; }
    /// An optimal link forest. Requires a finite value.
    [[nodiscard]] LinkForest reconstruct() const;

private:
    /// One point of a children staircase, with how it was obtained: child
    /// subtree (label b, qc planes, jc landings) added to entry `previous` of
    /// kids(q - qc, j - 1 - jc). b = -1 for the empty multiset.
    struct KidStep
    {
        Time tau = 0;
        Cost cost = 0;
        int b = -1, qc = 0, jc = 0, previous = -1;
    };

    [[nodiscard]] std::vector<KidStep>& kids(int q, int j) noexcept;
    [[nodiscard]] const std::vector<KidStep>& kids(int q, int j) const noexcept;
    [[nodiscard]] Cost& sub(int a, int q, int j) noexcept;
    [[nodiscard]] Cost sub(int a, int q, int j) const noexcept;
    [[nodiscard]] Cost& root(int q, int j) noexcept;
    [[nodiscard]] Cost root(int q, int j) const noexcept;
    [[nodiscard]] Cost forest(int planes, int j) const noexcept;

    // Reconstruction helpers: append the planes of a subtree to `out`.
    void buildKids(int q, int j, int step, int parentIndex, LinkForest& out) const;
    void buildNode(int q, int j, int label, Time budget, int parentIndex, LinkForest& out) const;

    const ReducedInstance& r_;
    const OnePlaneTable& G_;
    Time T_;
    int Q_, s_;
    std::size_t S_;
    std::vector<std::vector<KidStep>> kids_;
    std::vector<Cost> sub_, root_, forest_;
    Cost value_ = kInfCost;
};

/// ForestProgram(...).value().
[[nodiscard]] Cost forestCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, int maxTreePlanes, LevelStats* stats = nullptr);
} // namespace zeno
