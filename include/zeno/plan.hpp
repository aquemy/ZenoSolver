#pragma once

#include <zeno/forest.hpp>
#include <zeno/instance.hpp>
#include <zeno/reduce.hpp>

#include <string>
#include <vector>

namespace zeno
{
/// Locations of a plan: 0 is C_I, 1..n the central cities (city i of the
/// instance is location i + 1), n + 1 is C_G.
struct Leg
{
    int from = 0, to = 0;
    Time depart = 0, arrive = 0;
    int passenger = -1; ///< passenger carried, -1 when empty
    auto operator<=>(const Leg&) const = default;
};

/// A timed plan: the legs of every plane, in order. Boarding and debarking
/// are instantaneous; a passenger is aboard exactly the legs that name it.
struct Plan
{
    std::vector<std::vector<Leg>> planes;
};

/// The plan of Theorem 4.1 for a link forest of the reduced instance r of
/// `instance`: every plane first drops one passenger per child edge
/// (C_I -> b -> C_I), then flies its filler as alternating crossings
/// (C_I -> x -> C_G carrying a passenger, C_G -> x -> C_I empty, ...), then
/// picks up the passenger its parent dropped (C_G -> a -> C_G), waiting if
/// needed. Legs to and from C_I take d, legs to and from C_G take dbar.
/// Symmetric instances: cost c(X), makespan 2 * scale * max_k delta(X_k);
/// non-symmetric ones: a pick-up may wait for its drop-off, and the
/// simulated makespan (checkPlan) is the truth.
[[nodiscard]] Plan buildPlan(const Instance& instance, const ReducedInstance& r, const LinkForest& forest);

/// The instance with C_I and C_G exchanged (d and dbar swapped).
[[nodiscard]] Instance mirrored(const Instance& instance);

/// Time reversal: a plan of mirrored(instance) becomes a plan of `instance`
/// with the same cost and makespan (each leg reversed and C_I, C_G
/// exchanged; n is the number of central cities). It turns plans where
/// every plane picks up at most once into plans where every plane drops off
/// at most once.
[[nodiscard]] Plan mirrorPlan(const Plan& plan, int n);

struct PlanCheck
{
    bool ok = false;
    std::string error; ///< first violated rule when !ok
    Cost cost = 0;
    Time makespan = 0;
};

/// Simulates a plan against the model of doc/theory/exact-front.md, sharing
/// no code with buildPlan: every plane starts in C_I at time >= 0, chains its
/// legs (each leg leaves where the previous one arrived, no earlier, and
/// lasts the flight's duration) and ends in C_G; there is no C_I - C_G
/// flight, and central-to-central flights are rejected (the front never needs
/// them under (S) with (A1) or (AΔ), Theorem 4.5, nor under
/// (A1-NS), Corollary 5.6); every passenger 0..t-1 starts in C_I, rides
/// a time-ordered chain of legs and ends in C_G; a leg carries at most one
/// passenger. Cost = sum of the landing costs, makespan = last arrival.
[[nodiscard]] PlanCheck checkPlan(const Instance& instance, const Plan& plan);
} // namespace zeno
