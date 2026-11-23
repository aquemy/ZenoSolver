#pragma once

#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>

#include <cstdint>

namespace zeno
{
/// Work counters of the level evaluations (summed over calls).
struct LevelStats
{
    std::uint64_t states = 0; ///< DP cells written
    std::uint64_t relaxations = 0; ///< candidate transitions examined
};

/// The value functions of a level T (half makespan): the cheapest partition of
/// the s = 2t - p landings into p non-empty groups whose durations each sum to
/// at most T.
///
/// - relaxedCost: no admissibility constraint. A lower bound on E(T) for
///   every symmetric instance, central flights included (lemma R).
/// - forestCost: admissible partitions given by a link forest whose trees have
///   at most `maxTreePlanes` planes. A plane u holds an odd filler R_u plus
///   one landing per incident edge, an edge labelled a putting a landing in a
///   at both ends; |X_u| - deg(u) is odd. Every such partition is admissible,
///   so forestCost is an upper bound on E(T); with maxTreePlanes >=
///   ReducedInstance::maxTree() it is E(T) (link-forest lemma).
///   maxTreePlanes = 2 gives the pairs bound U, 3 the bound U3.
///
/// Both return kInfCost when no partition exists. G must cover the level T and
/// at least maxGroup() landings.
[[nodiscard]] Cost relaxedCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, LevelStats* stats = nullptr);
[[nodiscard]] Cost forestCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, int maxTreePlanes, LevelStats* stats = nullptr);
} // namespace zeno
