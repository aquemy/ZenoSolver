#include <zeno/forest.hpp>

#include <algorithm>
#include <stdexcept>
#include <vector>

namespace zeno
{
namespace
{
void checkLevel(const ReducedInstance& r, const OnePlaneTable& G, Time T)
{
    if(T < 0 || T > G.maxLevel() || G.maxLandings() < r.maxGroup())
        throw std::invalid_argument("forest: the one-plane table does not cover the level");
}

std::size_t at(int v) { return static_cast<std::size_t>(v); }

/// forest[P][J]: cheapest way to cover P planes and J landings with trees,
/// root(q, j) being the cheapest tree with q planes and j landings.
template<class RootCost>
std::vector<Cost> combineTrees(int p, int s, int maxTree, RootCost root, LevelStats* stats)
{
    const auto width = at(s + 1);
    std::vector<Cost> forest(at(p + 1) * width, kInfCost);
    forest[0] = 0;
    for(int planes = 1; planes <= p; ++planes)
        for(int q = 1; q <= std::min(maxTree, planes); ++q)
            for(int j = 1; j <= s; ++j)
            {
                const Cost tree = root(q, j);
                if(isInf(tree))
                    continue;
                const Cost* before = forest.data() + at(planes - q) * width;
                Cost* after = forest.data() + at(planes) * width;
                for(int J = j; J <= s; ++J)
                    if(!isInf(before[J - j]))
                        after[J] = std::min(after[J], before[J - j] + tree);
                if(stats)
                    stats->relaxations += at(s - j + 1);
            }
    return forest;
}
} // namespace

std::vector<int> LinkForest::group(std::size_t k) const
{
    std::vector<int> g = planes[k].filler;
    if(planes[k].parent >= 0)
        g.push_back(planes[k].parentCity);
    for(std::size_t child : children(k))
        g.push_back(planes[child].parentCity);
    std::ranges::sort(g);
    return g;
}

std::vector<std::size_t> LinkForest::children(std::size_t k) const
{
    std::vector<std::size_t> out;
    for(std::size_t i = 0; i < planes.size(); ++i)
        if(planes[i].parent == static_cast<int>(k))
            out.push_back(i);
    return out;
}

Cost relaxedCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, LevelStats* stats)
{
    checkLevel(r, G, T);
    // Every group is a one-plane tree with any positive number of landings.
    const auto forest = combineTrees(r.p, r.landings(), 1, [&](int, int m) {
        return m <= r.maxGroup() ? G(m, T) : kInfCost;
    }, stats);
    return forest.back();
}

Cost& ForestProgram::kids(int q, int j, Time tau) noexcept { return kids_[(at(q) * S_ + at(j)) * W_ + static_cast<std::size_t>(tau)]; }
Cost ForestProgram::kids(int q, int j, Time tau) const noexcept { return kids_[(at(q) * S_ + at(j)) * W_ + static_cast<std::size_t>(tau)]; }
Cost& ForestProgram::sub(int a, int q, int j) noexcept { return sub_[(at(a) * at(Q_) + at(q - 1)) * S_ + at(j)]; }
Cost ForestProgram::sub(int a, int q, int j) const noexcept { return sub_[(at(a) * at(Q_) + at(q - 1)) * S_ + at(j)]; }
Cost& ForestProgram::root(int q, int j) noexcept { return root_[at(q) * S_ + at(j)]; }
Cost ForestProgram::root(int q, int j) const noexcept { return root_[at(q) * S_ + at(j)]; }
Cost ForestProgram::forest(int planes, int j) const noexcept { return forest_[at(planes) * S_ + at(j)]; }

ForestProgram::ForestProgram(const ReducedInstance& r, const OnePlaneTable& G, Time T, int maxTreePlanes, LevelStats* stats)
    : r_(r)
    , G_(G)
    , T_(T)
    , Q_(std::max(1, std::min(maxTreePlanes, r.p)))
    , s_(r.landings())
    , S_(at(r.landings() + 1))
    , W_(static_cast<std::size_t>(T + 1))
{
    checkLevel(r, G, T);
    const int n = r.n(), s = s_, Q = Q_;
    kids_.assign(at(Q) * S_ * W_, kInfCost);
    sub_.assign(at(n) * at(Q) * S_, kInfCost);
    root_.assign(at(Q + 1) * S_, kInfCost);
    kids(0, 0, 0) = 0;

    // kids(q, j, tau): the children of one plane: q planes and j landings in
    // total, counting the subtrees and the plane's own copy of each child edge
    // label; tau is the sum of the child labels' durations, the part of the
    // plane's load taken by its child edges.
    // sub(a, q, j): a subtree of q planes and j landings hanging from its
    // parent by an edge labelled a (its root's copy of a included).
    // root(q, j): a whole tree.
    for(int q = 1; q <= Q; ++q)
    {
        // A plane with q - 1 descendants: its children plus an odd filler.
        const bool childAllowed = q <= Q - 1;
        for(Time tau = 0; tau <= T; ++tau)
            for(int jk = 0; jk < s; ++jk)
            {
                const Cost k = kids(q - 1, jk, tau);
                if(isInf(k))
                    continue;
                const Time rootBudget = T - tau;
                for(int rr = 1; jk + rr <= s && rr <= G.maxLandings(); rr += 2)
                {
                    const Cost asRoot = G(rr, rootBudget);
                    if(!isInf(asRoot))
                        root(q, jk + rr) = std::min(root(q, jk + rr), k + asRoot);
                    if(!childAllowed || jk + rr + 1 > s)
                        continue;
                    for(int a = 0; a < n; ++a)
                    {
                        const Cost filler = G(rr, rootBudget - r.d[at(a)]);
                        if(isInf(filler))
                            break; // d increases with a: less budget
                        Cost& cell = sub(a, q, jk + rr + 1);
                        cell = std::min(cell, r.c[at(a)] + k + filler);
                    }
                    if(stats)
                        stats->relaxations += at(n) + 1;
                }
            }
        if(!childAllowed)
            break;

        // kids(q, ., .) = kids(q - qc, ., .) plus one child subtree of qc planes.
        for(int b = 0; b < n; ++b)
        {
            const Time db = r.d[at(b)];
            if(db > T)
                break;
            const Cost cb = r.c[at(b)];
            for(int qc = 1; qc <= q; ++qc)
                for(int jc = 2; jc + 1 <= s; ++jc)
                {
                    const Cost child = sub(b, qc, jc);
                    if(isInf(child))
                        continue;
                    const Cost item = cb + child;
                    for(int j = jc + 1; j <= s; ++j)
                    {
                        const Cost* before = &kids(q - qc, j - 1 - jc, 0);
                        Cost* after = &kids(q, j, 0);
                        for(Time tau = db; tau <= T; ++tau)
                            after[tau] = std::min(after[tau], before[tau - db] + item);
                    }
                    if(stats)
                        stats->relaxations += at(s - jc) * static_cast<std::size_t>(T - db + 1);
                }
        }
        // before[] may hold kInfCost; kInfCost + item stays below overflow and
        // above kInfCost, so clamp the new layer.
        for(int j = 0; j <= s; ++j)
        {
            Cost* row = &kids(q, j, 0);
            for(std::size_t tau = 0; tau < W_; ++tau)
                row[tau] = std::min(row[tau], kInfCost);
        }
        if(stats)
            stats->states += S_ * W_;
    }

    forest_ = combineTrees(r.p, s, Q, [&](int q, int j) { return root(q, j); }, stats);
    value_ = forest(r.p, s);
}

void ForestProgram::buildNode(int q, int j, int label, Time budget, int parentIndex, LinkForest& out) const
{
    // budget: the node's load limit for its children and filler.
    const Cost target = label >= 0 ? sub(label, q, j) : root(q, j);
    const int own = label >= 0 ? 1 : 0;
    const Cost labelCost = label >= 0 ? r_.c[at(label)] : 0;
    for(Time tau = 0; tau <= budget; ++tau)
        for(int rr = 1; rr + own <= j && rr <= G_.maxLandings(); rr += 2)
        {
            const int jk = j - own - rr;
            const Cost k = kids(q - 1, jk, tau);
            const Cost filler = G_(rr, budget - tau);
            if(isInf(k) || isInf(filler) || labelCost + k + filler != target)
                continue;
            const int index = static_cast<int>(out.planes.size());
            out.planes.push_back({G_.witness(rr, budget - tau), parentIndex, label});
            buildKids(q - 1, jk, tau, index, out);
            return;
        }
    throw std::logic_error("ForestProgram::reconstruct: no decomposition of a tree node");
}

void ForestProgram::buildKids(int q, int j, Time tau, int parentIndex, LinkForest& out) const
{
    if(q == 0)
    {
        if(j != 0 || tau != 0)
            throw std::logic_error("ForestProgram::reconstruct: leftover children");
        return;
    }
    const Cost target = kids(q, j, tau);
    for(int b = 0; b < r_.n(); ++b)
    {
        const Time db = r_.d[at(b)];
        if(db > tau)
            break;
        for(int qc = 1; qc <= q; ++qc)
            for(int jc = 2; jc + 1 <= j; ++jc)
            {
                const Cost child = sub(b, qc, jc);
                const Cost before = kids(q - qc, j - 1 - jc, tau - db);
                if(isInf(child) || isInf(before) || before + r_.c[at(b)] + child != target)
                    continue;
                buildNode(qc, jc, b, T_ - db, parentIndex, out);
                buildKids(q - qc, j - 1 - jc, tau - db, parentIndex, out);
                return;
            }
    }
    throw std::logic_error("ForestProgram::reconstruct: no decomposition of a children multiset");
}

LinkForest ForestProgram::reconstruct() const
{
    if(isInf(value_))
        throw std::invalid_argument("ForestProgram::reconstruct: the level is infeasible");
    LinkForest out;
    int planes = r_.p, J = s_;
    while(planes > 0)
    {
        bool found = false;
        for(int q = 1; q <= std::min(Q_, planes) && !found; ++q)
            for(int j = 1; j <= J && !found; ++j)
            {
                const Cost tree = root(q, j), rest = forest(planes - q, J - j);
                if(isInf(tree) || isInf(rest) || tree + rest != forest(planes, J))
                    continue;
                buildNode(q, j, -1, T_, -1, out);
                planes -= q;
                J -= j;
                found = true;
            }
        if(!found)
            throw std::logic_error("ForestProgram::reconstruct: no decomposition of the forest");
    }
    return out;
}

Cost forestCost(const ReducedInstance& r, const OnePlaneTable& G, Time T, int maxTreePlanes, LevelStats* stats)
{
    return ForestProgram(r, G, T, maxTreePlanes, stats).value();
}
} // namespace zeno
