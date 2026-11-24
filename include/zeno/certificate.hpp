#pragma once

#include <zeno/instance.hpp>
#include <zeno/plan.hpp>
#include <zeno/solve.hpp>

#include <iosfwd>
#include <string>
#include <vector>

namespace zeno
{
/// How a checker establishes a lower bound (doc/certificate-format.md).
enum class GapBound
{
    Relaxed,    ///< recompute L at the level (lemma R; no assumption on central flights)
    Forest,     ///< recompute E with the link-forest DP (symmetric; needs (A1) or (AΔ):
                ///< Theorems 4.7 and 4.10, Corollary 4.12)
    Roles,      ///< v2: recompute the role relaxation (needs A1-NS)
    Lagrangian, ///< v2: evaluate the Lagrangian bound at the listed multipliers (needs A1-NS)
    Balanced,   ///< v2: rerun the exact balanced role program (needs A1-NS)
    Search,     ///< v2: rerun the exhaustive search over role configurations with exact
                ///< schedules (needs A1-NS)
    Closed,     ///< fastest point only: the closed form 2 d_min ceil(s / p) (symmetric)
};

/// A front certificate. Version 1 covers symmetric instances with `relaxed`
/// and `forest` gaps and the closed-form fastest point; version 2 adds
/// non-symmetric instances, the kinds roles / lagrangian / balanced, and a
/// `fastest` line naming the bound that rules out faster plans.
struct Certificate
{
    int version = 1;
    Instance instance;
    std::vector<std::string> assumptions; ///< e.g. "S", "A1" (or "A1|AD"), "A1-NS"
    Front front;                          ///< by increasing makespan
    std::vector<Plan> plans;              ///< plans[i] realises front[i]
    std::vector<GapBound> gaps;           ///< gaps[i] for the gap between points i and i + 1
    std::vector<std::vector<Cost>> multipliers; ///< v2: per gap, per original city, for Lagrangian gaps
    GapBound fastest = GapBound::Closed;  ///< v2: the bound below the fastest point
};

/// What `forest` gaps rely on: the central flights satisfy (A1) or the
/// triangle inequality (AΔ). By Theorem 4.7 (under (A1)) and Theorem 4.10 with
/// Corollary 4.12 (under (AΔ)), E is then a lower bound for every plan.
/// checkCertificate reports this token, and accepts it in a certificate as a
/// synonym of "A1", the token that certificates list for forest gaps: the Lean
/// checker reads "A1", and is proved sound under (A1) (Cert.check_sound_A1)
/// and under (AΔ) (Cert.check_sound_ATri).
inline constexpr const char* kA1OrTriangle = "A1|AD";

/// The gap kinds of a symmetric front: `relaxed` when L already reaches the
/// cost of the gap (sound whatever the central flights), `forest` otherwise.
[[nodiscard]] std::vector<GapBound> symmetricGaps(const Instance& instance, const Front& front);

/// The certificate of a solved front (requires SolveOptions::plans), with
/// the gaps of symmetricGaps. When a gap is `forest`, it lists "A1" if the
/// central flights satisfy (A1) or (AΔ), as the default and metric tables do,
/// and throws std::invalid_argument if they satisfy neither (Example 4.13).
[[nodiscard]] Certificate makeCertificate(const Instance& instance, const SolveResult& result);

struct BracketResult;
/// Version 2 certificate of an exact non-symmetric bracket (requires
/// BracketResult::exact() and SolveOptions::plans); throws
/// std::invalid_argument otherwise, and when a gap needs (A1-NS) that the
/// central flights violate.
[[nodiscard]] Certificate makeBracketCertificate(const Instance& instance, const BracketResult& result);

void writeCertificate(std::ostream& out, const Certificate& certificate);
/// Throws std::runtime_error with the line number on a syntax error.
[[nodiscard]] Certificate readCertificate(std::istream& in);

struct CertificateCheck
{
    bool ok = false;
    std::vector<std::string> errors;  ///< every failed obligation
    std::vector<std::string> relied; ///< assumptions the accepted obligations needed
};

/// Reference checker: verifies the four obligations of the format. It uses
/// the library's dynamic programs for the gap bounds, so it is a consistency
/// check of the solver, not an independent proof; the Lean checker is.
[[nodiscard]] CertificateCheck checkCertificate(const Certificate& certificate);
} // namespace zeno
