#include <zeno/forest.hpp>

#include <algorithm>
#include <stdexcept>
#include <vector>

namespace zeno
{
namespace
{
/// Dense 3-index table with kInfCost default.
class Table3
{
public:
    Table3(std::size_t a, std::size_t b, std::size_t c)
        : b_(b), c_(c), v_(a * b * c, kInfCost) {}
    Cost& at(std::size_t i, std::size_t j, std::size_t k) noexcept { return v_[(i * b_ + j) * c_ + k]; }
    Cost at(std::size_t i, std::size_t j, std::size_t k) const noexcept { return v_[(i * b_ + j) * c_ + k]; }

private:
    std::size_t b_, c_;
    std::vector<Cost> v_;
};

void checkLevel(const ReducedInstance& r, const OnePlaneTable& G, Time T)
{
    if(T < 0 || T > G.maxLevel() || G.maxLandings() < r.maxGroup())
        throw std::invalid_argument("forest: the one-plane table does not cover the level");
}

/// Forest[P][J] = cheapest way to cover P planes and J landings with trees from
/// `root` (root(q, j) = cheapest tree with q planes and j landings).
template<class RootCost>
Cost combineTrees(int p, int s, int maxTree, RootCost root, LevelStats* stats)
{
    const auto width = static_cast<std::size_t>(s + 1);
    std::vector<Cost> forest(static_cast<std::size_t>(p + 1) * width, kInfCost);
    forest[0] = 0;
    for(int planes = 1; planes <= p; ++planes)
        for(int q = 1; q <= std::min(maxTree, planes); ++q)
            for(int j = 1; j <= s; ++j)
            {
                const Cost tree = root(q, j);
                if(isInf(tree))
                    continue;
                const Cost* before = forest.data() + static_cast<std::size_t>(planes - q) * width;
                Cost* after = forest.data() + static_cast<std::size_t>(planes) * width;
                for(int J = j; J <= s; ++J)
                    if(!isInf(before[J - j]))
                        after[J] = std::min(after[J], before[J - j] + tree);
                if(stats)
                    stats->relaxations += static_cast<std::uint64_t>(s - j + 1);
            }
    return forest[static_cast<std::size_t>(p) * width + static_cast<std::size_t>(s)];
}
} // namespace

Cost relaxedCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, LevelStats* stats)
{
    checkLevel(r, G, T);
    // Every group is a tree with one plane and any positive number of landings.
    return combineTrees(r.p, r.landings(), 1, [&](int, int m) {
        return m <= r.maxGroup() ? G(m, T) : kInfCost;
    }, stats);
}

Cost forestCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, int maxTreePlanes, LevelStats* stats)
{
    checkLevel(r, G, T);
    const int p = r.p, s = r.landings(), n = r.n();
    const int Q = std::max(1, std::min(maxTreePlanes, p));
    const auto S = static_cast<std::size_t>(s + 1);
    const auto W = static_cast<std::size_t>(T + 1);
    const auto qs = static_cast<std::size_t>(Q);

    // kids(q, j, tau): children multisets hanging from one plane: q planes and
    // j landings in total, counting the subtrees and the plane's own copy of
    // each child edge label; tau = sum of the child labels' durations, i.e.
    // the part of the plane's load taken by its child edges.
    Table3 kids(qs, S, W);
    kids.at(0, 0, 0) = 0;
    // sub(a, q, j): a subtree of q planes and j landings whose root hangs from
    // its parent by an edge labelled a (the root's copy of a included).
    Table3 sub(static_cast<std::size_t>(n), qs, S);
    // root(q, j): a whole tree.
    std::vector<Cost> root((qs + 1) * S, kInfCost);

    for(int q = 1; q <= Q; ++q)
    {
        // A plane with q - 1 descendants: kids + odd filler R (|R| = rr).
        const bool childAllowed = q <= Q - 1;
        for(std::size_t tau = 0; tau < W; ++tau)
            for(int jk = 0; jk < s; ++jk)
            {
                const Cost k = kids.at(static_cast<std::size_t>(q - 1), static_cast<std::size_t>(jk), tau);
                if(isInf(k))
                    continue;
                const Time rootBudget = T - static_cast<Time>(tau);
                for(int rr = 1; jk + rr <= s && rr <= G.maxLandings(); rr += 2)
                {
                    const Cost asRoot = G(rr, rootBudget);
                    if(!isInf(asRoot))
                    {
                        Cost& cell = root[static_cast<std::size_t>(q) * S + static_cast<std::size_t>(jk + rr)];
                        cell = std::min(cell, k + asRoot);
                    }
                    if(!childAllowed || jk + rr + 1 > s)
                        continue;
                    for(int a = 0; a < n; ++a)
                    {
                        const Cost filler = G(rr, rootBudget - r.d[static_cast<std::size_t>(a)]);
                        if(isInf(filler))
                            break; // d is increasing: larger a has less budget
                        Cost& cell = sub.at(static_cast<std::size_t>(a), static_cast<std::size_t>(q - 1), static_cast<std::size_t>(jk + rr + 1));
                        cell = std::min(cell, r.c[static_cast<std::size_t>(a)] + k + filler);
                    }
                    if(stats)
                        stats->relaxations += static_cast<std::uint64_t>(n) + 1;
                }
            }
        if(!childAllowed)
            break;

        // kids(q, ., .) from kids(q - qc, ., .) plus one child subtree of qc planes.
        for(int b = 0; b < n; ++b)
        {
            const auto db = static_cast<std::size_t>(r.d[static_cast<std::size_t>(b)]);
            const Cost cb = r.c[static_cast<std::size_t>(b)];
            if(db >= W)
                break;
            for(int qc = 1; qc <= q; ++qc)
                for(int jc = 2; jc + 1 <= s; ++jc)
                {
                    const Cost child = sub.at(static_cast<std::size_t>(b), static_cast<std::size_t>(qc - 1), static_cast<std::size_t>(jc));
                    if(isInf(child))
                        continue;
                    const Cost item = cb + child;
                    const auto from = static_cast<std::size_t>(q - qc);
                    for(int j = jc + 1; j <= s; ++j)
                    {
                        const auto jFrom = static_cast<std::size_t>(j - 1 - jc);
                        for(std::size_t tau = db; tau < W; ++tau)
                        {
                            const Cost before = kids.at(from, jFrom, tau - db);
                            if(isInf(before))
                                continue;
                            Cost& cell = kids.at(static_cast<std::size_t>(q), static_cast<std::size_t>(j), tau);
                            cell = std::min(cell, before + item);
                        }
                    }
                    if(stats)
                        stats->relaxations += static_cast<std::uint64_t>(s - jc) * (W - db);
                }
        }
        if(stats)
            stats->states += S * W;
    }

    return combineTrees(p, s, Q, [&](int q, int j) {
        return root[static_cast<std::size_t>(q) * S + static_cast<std::size_t>(j)];
    }, stats);
}
} // namespace zeno
