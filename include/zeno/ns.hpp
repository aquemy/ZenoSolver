#pragma once

#include <zeno/instance.hpp>
#include <zeno/plan.hpp>
#include <zeno/solve.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace zeno
{
/// How a gap of the non-symmetric bracket is closed.
enum class GapProof : std::uint8_t
{
    Open,      ///< neither lower bound reaches the cost: the true front may hold a point in the gap
    Relaxed,   ///< lemma R with role weight min(2 d, 2 dbar): no assumption on central flights
    Roles,     ///< role relaxation (each plane an odd number >= 1 of crossings, and the
               ///< loads add up to fill(X)): needs Theorem 6.1 of the theory note
               ///< (assumption A1-NS)
};

/// A certified bracket of the Pareto front of a (non-symmetric) instance.
///
/// `upper` lists points achieved by simulated plans: link forests whose
/// planes pick up at most once (or, by time reversal, drop off at most once),
/// so every point is a real plan and the true front weakly dominates it.
/// For the gap between upper[i] and upper[i + 1], gapLower[i] is a lower
/// bound on the cost of every plan with makespan < upper[i + 1].makespan; the
/// gap is closed when it reaches upper[i].cost. The front is exact when the
/// fastest makespan is certified and every gap is closed.
struct BracketResult
{
    Front upper;
    std::vector<Plan> plans;            ///< plans[i] realises upper[i] (SolveOptions::plans)
    Time fastestLower = 0;              ///< no plan has a smaller makespan
    GapProof fastestProof = GapProof::Relaxed; ///< which bound gives fastestLower
    std::vector<Cost> gapLower;         ///< per gap
    std::vector<GapProof> gapProof;     ///< per gap
    [[nodiscard]] bool exact() const;
    /// Assumptions the closed gaps rely on ("A1-NS" when a Roles gap is used).
    [[nodiscard]] std::vector<std::string> assumptions() const;
    SolveStats stats;
};

/// Certified bracket of the front of any valid instance, symmetric or not.
/// For symmetric instances prefer solveFront, which is exact.
[[nodiscard]] BracketResult solveBracket(const Instance& instance, const SolveOptions& options = {});
} // namespace zeno
