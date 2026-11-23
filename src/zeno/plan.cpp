#include <zeno/plan.hpp>

#include <algorithm>
#include <map>
#include <stdexcept>
#include <string>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }
} // namespace

Plan buildPlan(const Instance& instance, const ReducedInstance& r, const LinkForest& forest)
{
    if(static_cast<int>(forest.planes.size()) != r.p)
        throw std::invalid_argument("buildPlan: the forest needs one node per plane");
    const int goal = instance.n() + 1;
    // Location of a reduced city, and its flight durations to C_I and to C_G.
    const auto location = [&](int reduced) { return r.original[at(reduced)] + 1; };
    const auto west = [&](int reduced) { return instance.d[at(r.original[at(reduced)])]; };
    const auto east = [&](int reduced) { return instance.dbar[at(r.original[at(reduced)])]; };

    Plan plan;
    plan.planes.resize(forest.planes.size());
    int nextPassenger = 0;
    // dropTime[child] / dropped[child]: when and which passenger the parent of
    // `child` left in the child's parent city.
    std::vector<Time> dropTime(forest.planes.size(), 0);
    std::vector<int> dropped(forest.planes.size(), -1);

    // Parents come before their children in a reconstructed forest, but do not
    // rely on it: schedule in an order where every parent precedes its children.
    std::vector<std::size_t> order;
    std::vector<bool> placed(forest.planes.size(), false);
    while(order.size() < forest.planes.size())
    {
        const std::size_t before = order.size();
        for(std::size_t k = 0; k < forest.planes.size(); ++k)
            if(!placed[k] && (forest.planes[k].parent < 0 || placed[at(forest.planes[k].parent)]))
            {
                placed[k] = true;
                order.push_back(k);
            }
        if(order.size() == before)
            throw std::invalid_argument("buildPlan: the parent relation has a cycle");
    }

    for(std::size_t k : order)
    {
        auto& legs = plan.planes[k];
        Time now = 0;
        const auto fly = [&](int from, int to, Time leave, Time length, int passenger) {
            legs.push_back({from, to, leave, leave + length, passenger});
            now = leave + length;
        };
        // 1. Drop-offs, one per child edge.
        for(std::size_t child : forest.children(k))
        {
            const int b = forest.planes[child].parentCity;
            const int passenger = nextPassenger++;
            fly(0, location(b), now, west(b), passenger);
            dropTime[child] = now;
            dropped[child] = passenger;
            fly(location(b), 0, now, west(b), -1);
        }
        // 2. The filler as alternating crossings, starting and ending with A.
        const auto& filler = forest.planes[k].filler;
        if(filler.size() % 2 == 0)
            throw std::invalid_argument("buildPlan: a filler must have an odd size");
        for(std::size_t i = 0; i < filler.size(); ++i)
        {
            const int x = filler[i];
            if(i % 2 == 0)
            {
                const int passenger = nextPassenger++;
                fly(0, location(x), now, west(x), passenger);
                fly(location(x), goal, now, east(x), passenger);
            }
            else
            {
                fly(goal, location(x), now, east(x), -1);
                fly(location(x), 0, now, west(x), -1);
            }
        }
        // 3. The pick-up of the passenger the parent dropped.
        if(forest.planes[k].parent >= 0)
        {
            const int a = forest.planes[k].parentCity;
            fly(goal, location(a), now, east(a), -1);
            fly(location(a), goal, std::max(now, dropTime[k]), east(a), dropped[k]);
        }
    }
    if(nextPassenger != instance.t)
        throw std::logic_error("buildPlan: the forest carries " + std::to_string(nextPassenger) + " passengers, not t = " + std::to_string(instance.t));
    return plan;
}

Instance mirrored(const Instance& instance)
{
    Instance m = instance;
    std::swap(m.d, m.dbar);
    return m;
}

Plan mirrorPlan(const Plan& plan, int n)
{
    const auto flip = [n](int loc) { return loc == 0 ? n + 1 : loc == n + 1 ? 0 : loc; };
    Time end = 0;
    for(const auto& legs : plan.planes)
        for(const Leg& leg : legs)
            end = std::max(end, leg.arrive);
    Plan out;
    for(const auto& legs : plan.planes)
    {
        std::vector<Leg> reversed;
        for(auto it = legs.rbegin(); it != legs.rend(); ++it)
            reversed.push_back({flip(it->to), flip(it->from), end - it->arrive, end - it->depart, it->passenger});
        out.planes.push_back(std::move(reversed));
    }
    return out;
}

PlanCheck checkPlan(const Instance& instance, const Plan& plan)
{
    PlanCheck result;
    const int n = instance.n(), goal = n + 1;
    const auto fail = [&](std::string why) {
        result.ok = false;
        result.error = std::move(why);
        return result;
    };
    if(static_cast<int>(plan.planes.size()) != instance.p)
        return fail("the plan has " + std::to_string(plan.planes.size()) + " planes, the instance " + std::to_string(instance.p));

    const auto central = [&](int loc) { return loc >= 1 && loc <= n; };
    // Passenger legs, gathered from every plane.
    std::map<int, std::vector<Leg>> rides;
    Cost cost = 0;
    Time makespan = 0;
    for(std::size_t k = 0; k < plan.planes.size(); ++k)
    {
        const std::string who = "plane " + std::to_string(k);
        int location = 0;
        Time time = 0;
        if(plan.planes[k].empty())
            return fail(who + " never leaves C_I");
        for(const Leg& leg : plan.planes[k])
        {
            if(leg.from < 0 || leg.from > goal || leg.to < 0 || leg.to > goal)
                return fail(who + " uses an unknown location");
            if(leg.from != location)
                return fail(who + " leaves location " + std::to_string(leg.from) + " but is at " + std::to_string(location));
            if(leg.depart < time)
                return fail(who + " leaves before it arrives");
            Time length = 0;
            if(central(leg.from) == central(leg.to))
            {
                if(central(leg.from))
                    return fail(who + " flies between two central cities");
                return fail(who + " flies between C_I and C_G, or stays put");
            }
            const int city = central(leg.from) ? leg.from : leg.to;
            const int hub = central(leg.from) ? leg.to : leg.from;
            length = hub == 0 ? instance.d[at(city - 1)] : instance.dbar[at(city - 1)];
            if(leg.arrive != leg.depart + length)
                return fail(who + " has a flight of the wrong duration");
            if(central(leg.to))
                cost += instance.c[at(leg.to - 1)];
            if(leg.passenger >= 0)
            {
                if(leg.passenger >= instance.t)
                    return fail(who + " carries an unknown passenger");
                rides[leg.passenger].push_back(leg);
            }
            location = leg.to;
            time = leg.arrive;
        }
        if(location != goal)
            return fail(who + " does not end in C_G");
        makespan = std::max(makespan, time);
    }
    for(int passenger = 0; passenger < instance.t; ++passenger)
    {
        const std::string who = "passenger " + std::to_string(passenger);
        auto it = rides.find(passenger);
        if(it == rides.end())
            return fail(who + " never leaves C_I");
        // Follow the passenger's route: from where it is, the earliest leg
        // leaving that location no earlier than it got there. Zero-duration
        // flights make times tie, locations do not.
        std::vector<Leg> legs = it->second;
        std::vector<bool> used(legs.size(), false);
        int location = 0;
        Time time = 0;
        for(std::size_t step = 0; step < legs.size(); ++step)
        {
            std::size_t best = legs.size();
            for(std::size_t i = 0; i < legs.size(); ++i)
                if(!used[i] && legs[i].from == location && legs[i].depart >= time &&
                   (best == legs.size() || std::pair(legs[i].depart, legs[i].arrive) < std::pair(legs[best].depart, legs[best].arrive)))
                    best = i;
            if(best == legs.size())
                return fail(who + " boards a flight where or when it is not");
            used[best] = true;
            location = legs[best].to;
            time = legs[best].arrive;
        }
        if(location != goal)
            return fail(who + " does not end in C_G");
    }
    result.ok = true;
    result.cost = cost;
    result.makespan = makespan;
    return result;
}
} // namespace zeno
