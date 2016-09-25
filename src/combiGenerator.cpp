#include <vector>
#include <combiGenerator.hpp>

int nextTuple(std::vector<int>& vec, const int n, const int k)
{
    int j;

    if(vec[k-1] < n - 1)
    {
        vec[k - 1]++;
        return(NEXT);
    }

    for(j = k - 2; j >= 0; j--)
        if(vec[j] != n - 1)
            break;

    if(j < 0)
        return(DONE);

    vec[j]++;

    for(j += 1; j < k; j++)
        vec[j] = vec[j - 1];

    return(NEXT);
}

int nextkPartition(std::vector<int>& vec, unsigned int t, unsigned int n)
{
    int j;
    int r;
    int temp;

    if(t <= 1) {
        return(DONE);
    }

    if(vec[t-2] < vec[t-1] - 1)
    {
        vec[t-1]--;
        vec[t-2]++;
        return(NEXT);
    }

    r = vec[t-1] + vec[t-2] - 1;

    for(j = t-3; j >= 0; j--)
    {
        if(vec[j] < vec[t-1] - 1)
            break;

        r += vec[j];
    }

    if(j >= t) {
        return(DONE);
    }

    vec[j]++;

    temp = vec[j];

    for(j += 1; j < t-1; j++)
    {
        vec[j] = temp;
        r -= temp;
    }

    vec[t-1] = r;
    int s = NEXT;
    while(vec[t-1] >= n) {
        s = nextkPartition(vec, t, n);
    }
    return(s);
}

int generateLargestCombi(int S, int n, int t, std::vector<int>& e) {
    int k = std::min(S, n-1); // Max element that can be given
    int a = k;
    int pS = S;
    int i = t-1;
    while(pS > 0 && i >= 0) {
        if(pS - a >= 0) {
            e[i] = a;
            pS -= a;
            --i;
        }
        else {
            a = std::max(a - 1, pS);
        }
    }
    return pS;
}