#pragma once

#include <cstddef>
#include <utility>


struct ProbBound
{
    double lb;
    double ub;
};

struct StateSpace
{
    size_t* states;
    size_t* transitions;
    size_t* branches;
    ProbBound* probabilities;
    size_t* avoids;
    size_t* targets;
};

// This is the loader's own representation. Each solver translation unit converts it to the
// modest_mdp_t of its generated header and static_asserts the layout there, where both
// definitions are visible.
