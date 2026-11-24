#pragma once

#include <zeno/instance.hpp>

namespace zeno
{
/// Which assumptions of doc/theory/exact-front.md (§1.4) the flights of an
/// instance satisfy. Every pair of central cities has a flight
/// (Instance::centralFlight); C_I and C_G have none between them.
struct FlightAssumptions
{
    /// (A1), under (S): d_ij >= d_i + d_j for every central flight. With (S),
    /// it makes the front exact by Theorem 4.7 (Corollary 4.8). False for
    /// non-symmetric durations, where (A1-NS) takes its place.
    bool a1 = false;
    /// (AΔ): dur(a, b) <= dur(a, x) + dur(x, b) whenever the three flights
    /// exist, over C_I, C_G and the central cities. With (S), it makes the
    /// front exact by Theorem 4.10 (Corollary 4.12).
    bool triangle = false;
    /// (A1-NS): d_ij >= min(d_i + d_j, dbar_i + dbar_j) for every central
    /// flight. The non-symmetric bounds but lemma R need it (Theorem 6.1).
    bool a1ns = false;

    /// (A1) or (AΔ): the symmetric front is exact, and `forest` certificate
    /// gaps are sound (Corollary 4.12).
    [[nodiscard]] bool exactSymmetric() const noexcept { return a1 || triangle; }
};

/// Checks the assumptions in exact integer arithmetic, in O(n^3). The
/// instance must be valid (Instance::validate).
[[nodiscard]] FlightAssumptions checkFlights(const Instance& instance);
} // namespace zeno
