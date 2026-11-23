#pragma once

#include <zeno/instance.hpp>
#include <zeno/plan.hpp>
#include <zeno/solve.hpp>

#include <iosfwd>
#include <string>
#include <vector>

namespace zeno
{
/// How a checker establishes the lower bound of a gap (doc/certificate-format.md).
enum class GapBound
{
    Relaxed, ///< recompute L at the gap level (lemma R; needs only symmetry)
    Forest,  ///< recompute E with the link-forest DP (needs assumption A1)
};

/// A front certificate, format version 1.
struct Certificate
{
    Instance instance;
    std::vector<std::string> assumptions; ///< e.g. "S", "A1"
    Front front;                          ///< by increasing makespan
    std::vector<Plan> plans;              ///< plans[i] realises front[i]
    std::vector<GapBound> gaps;           ///< gaps[i] for the gap between points i and i + 1
};

/// The certificate of a solved front (requires SolveOptions::plans). A gap
/// gets `relaxed` when L already reaches the cost, `forest` otherwise.
[[nodiscard]] Certificate makeCertificate(const Instance& instance, const SolveResult& result);

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
