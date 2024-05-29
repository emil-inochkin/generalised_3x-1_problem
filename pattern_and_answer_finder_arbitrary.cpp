#include <iostream>
#include <algorithm>
#include <vector>
#include <queue>

#define COEFFICIENT 100000

using namespace std;

long long GCD(long long a, long long b)
{
  if (b == 0) return a;
  return GCD(b, a % b);
}

long long exp(int x, int n)
{
  if (n == 0) return 1;
  if (n & 1) return x * exp(x, n - 1);
  long long tmp = exp(x, n / 2);
  return tmp * tmp;
}

struct fraction
{
  long long a;
  long long b;
  static int max_num_len;

  fraction(long long num, long long denom)
  {
    a = num;
    b = denom;

    int len = num < 0;
    while (num) num /= 10, len++;
    max_num_len = max(max_num_len, len);
  }

  void simplify()
  {
    long long g = GCD(abs(a), b);
    a /= g;
    b /= g;
  }

  void print()
  {
    printf("%*lld/%lld", max_num_len, a, b);
  }
};

struct pattern
{
  vector <vector <int> > pat;
  int x, y, y_to_print;
  int size = 0;
  bool fixed = false;

  pattern() {;}

  pattern(int x_cor, int y_cor, int y_pr)
  {
    x = x_cor;
    y = y_cor;
    y_to_print = y_pr;
  }

  void fix()
  {
    if (!fixed) reverse(pat.begin(), pat.end());
    fixed = true;
  }

  void print()
  {
    cout << size << endl;
    cout << x << " " << y_to_print << endl;
    for (auto i : pat)
    {
      for (auto j : i)
      {
        if (j > 9) cout << (char)('A' + j - 10);
        else cout << j;
      }
      cout << endl;
    }
  }
};

vector<pair<int, int> > create_division_table(int p, int q)
{
  vector<pair<int, int> > A(p);
  for (int i = 0; i < p; i++)
  {
    int mult = i * q;
    int k = mult / p, r = mult % p;
    A[r] = {i, k};
  }
  
  return A;
}

vector<fraction> find_rational_solutions(int p, int q, int n, int seq_size, vector <pair <char, int> >& operations) 
{
  vector<fraction> solutions;
  long long b = exp(q, n) - exp(p, seq_size);
  for (int i = 0; i < n; i++)
  {
    long long p_pow = exp(p, seq_size), q_pow = 1;
    long long a = 0;
    for (int j = i; j < n + i; j++)
    {
      if (operations[j % n].first == 'S') p_pow /= p;
      a += operations[j % n].second * p_pow * q_pow;
      q_pow *= q;
    }

    if (b < 0) solutions.push_back(fraction(-a, -b));
    else solutions.push_back(fraction(a, b));
    solutions.back().simplify();
  }
  solutions.push_back(solutions[0]);

  return solutions;
}

void bfs(int i, int j, vector <vector <int> >& v, vector <vector <int> >& used, pattern& pat, int pat_num, int seq_size)
{
  used[i][j] = 1;
  queue <pair <pair <int, int>, int> > q;
  q.push({{i, j}, 0});
  int pat_size = 0;

  while (!q.empty())
  {
    i = q.front().first.first;
    j = q.front().first.second;
    int cnt = q.front().second;
    q.pop();
    pat_size++;

    if (cnt >= pat.pat.size()) pat.pat.push_back(vector <int> (0));
    pat.pat[cnt].push_back(pat_num);

    if (j != v[i].size() - 1 && v[i][j + 1] != pat_num)
    {
      pat.pat[cnt].push_back(v[i][j + 1]);
    }

    if (j != v[i].size() - 1 && v[i][j + 1] == pat_num && !used[i][j + 1])
    {
      q.push({{i, j + 1}, cnt});
      used[i][j + 1] = 1;
    }

    if (i > 1 && v[i - 1][j] == pat_num && !used[i - 1][j])
    {
      q.push({{i - 1, j}, cnt + 1});
      used[i - 1][j] = 1;
    }
    else if (i == 1 && v[i - 1][j] == pat_num && j + seq_size < v[i].size() - 1 && !used[v.size() - 1][j + seq_size])
    {
      q.push({{v.size() - 1, j + seq_size}, cnt + 1});
      used[v.size() - 1][j + seq_size] = 1;
    }
  }

  pat.size = pat_size;
}

void solve(int p, int q, int blocks, int n, vector <pair <char, int> >& operations)
{
  vector<pair<int, int> > A = create_division_table(p, q); // Division table

  int seq_size = 0; for (auto x : operations) seq_size += x.first == 'S'; // Number of S operations | Size of the sequences
  int curr_ind = seq_size; // Current index
  vector <vector <int> > v(n + 1, vector <int>(seq_size, -1)); // p-nary sequences | -1s used to denote empty cells
  vector <int> carry(n + 1, 0); // Carry from subtraction/addition
  vector <int> shift(n + 1, 0); // Carry from division
  
  for (int i = 0; i < n; i++)
  {
    if (operations[i].first == 'S') curr_ind--, v[i][curr_ind] = operations[i].second;
    else 
    {
      if (curr_ind != seq_size) v[i][curr_ind] += operations[i].second;
      else carry[i] = operations[i].second;
    }

    for (int j = curr_ind; j < seq_size; j++)
    {
      v[i][j] += carry[i]; carry[i] = 0;
      if (v[i][j] >= p) carry[i] = 1, v[i][j] -= p;
      if (v[i][j] < 0) carry[i] = -1, v[i][j] += p;

      int tmp = v[i][j] - shift[i], shift_carry = 0;
      if (tmp < 0)
      {
        shift_carry = 1;
        tmp += p;
      }
      v[i + 1][j] = A[tmp].first;
      shift[i] = A[tmp].second + shift_carry;
    }
  }

  curr_ind = seq_size;
  for (int k = 0; k < blocks; k++)
  {
    for (int counter = 0; counter < seq_size; counter++, curr_ind++)
    {
      v[0].push_back(v.back()[curr_ind - seq_size]);
      for (int i = 1; i <= n; i++)
      {
        v[i - 1][curr_ind] += carry[i - 1]; carry[i - 1] = 0;
        if (v[i - 1][curr_ind] >= p) carry[i - 1] = 1, v[i - 1][curr_ind] -= p;
        if (v[i - 1][curr_ind] < 0) carry[i - 1] = -1, v[i - 1][curr_ind] += p;

        int tmp = v[i - 1][curr_ind] - shift[i - 1], shift_carry = 0;
        if (tmp < 0)
        {
          shift_carry = 1;
          tmp += p;
        }
        v[i].push_back(A[tmp].first);
        shift[i - 1] = A[tmp].second + shift_carry;
      }
    }
  }

  vector<fraction> solutions = find_rational_solutions(p, q, n, seq_size, operations);
  
  for (int i = 0; i <= n; i++) 
  {
    reverse(v[i].begin(), v[i].end());
    // Remove if sequence print not needed
    solutions[i].print();
    cout << " = ";
    cout << "... | ";
    for (int j = 0; j < v[i].size(); j++)
    {
      if (v[i][j] == -1) //break;
      {
        cout << "  ";
        continue;
      }
      if (j && j % seq_size == 0) cout << "| "; // To comment if vertical bars are not needed
      if (v[i][j] < 10) cout << v[i][j] << " ";
      else cout << (char)(v[i][j] - 10 + 'A') << " ";
    }
    if (i != n)
    {
      cout << " | " << operations[i].first << " ";
      if (operations[i].second < 10) cout << operations[i].second;
      else cout << (char)(operations[i].second - 10 + 'A');
    }
    cout << endl;
    // Remove if sequence print not needed
  }

  if (solutions[0].b == 1)
  {
    cout << endl << "The answer is a" << (solutions[0].a < 0 ? "negative" : "positive") << "integer" << endl << endl;
    return;
  }
  
  vector <vector <int> > used(v.size(), vector <int>(v[0].size(), 0));

  pattern zero_pattern = pattern();
  for (int j = 0; j < v[0].size(); j++)
  {
    for (int i = n; i > 0; i--)
    {
      if (!used[i][j] && !v[i][j]) 
      {
        pattern new_pattern = pattern(i, j, v[0].size() - j);
        bfs(i, j, v, used, new_pattern, 0, seq_size);
        if (new_pattern.size >= zero_pattern.size) zero_pattern = new_pattern;
      }
    }
  }
  zero_pattern.fix();
  cout << endl;
  zero_pattern.print();
  cout << endl;

  pattern p_pattern = pattern();
  for (int j = 0; j < v[0].size(); j++)
  {
    for (int i = n; i > 0; i--)
    {
      if (!used[i][j] && v[i][j] == p - 1) 
      {
        pattern new_pattern = pattern(i, j, v[0].size() - j);
        bfs(i, j, v, used, new_pattern, p - 1, seq_size);
        if (new_pattern.size >= p_pattern.size) p_pattern = new_pattern;
      }
    }
  }
  p_pattern.fix();
  cout << endl;
  p_pattern.print();
  cout << endl;
}

int fraction::max_num_len = 1;

int main()
{
  int p; // Base
  int q; // q
  int blocks; // Number of blocks
  int n; // Number of rules
  while (cin >> p >> q >> n)
  {
    vector <pair <char, int> > v; // Operations
    for (int i = 0; i < n; i++)
    {
      char c; // Operation type
      char k, k2; // Operation description
      int num; // Operations description translated to decimal numbers
      cin >> c >> k;
      if (k == '-')
      {
        cin >> k2;
        if (k2 >= '0' && k2 <= '9') num = k2 - '0';
        else num = k2 - 'A' + 10;
        num = -num;
      }
      else
      {
        if (k >= '0' && k <= '9') num = k - '0';
        else num = k - 'A' + 10;
      }
      v.push_back({c, num});
    }
    blocks = n * COEFFICIENT;
    solve(p, q, blocks, n, v);
  }
}

/*
13 9
T -1
T -2
T -3
T -5
T -C
T 2
T 3
S 5
S 3

11 7 7
T 2
S -3
T -4
S 0
S 2
T -5
S 0

17 7 9
S 4
S G
S E
T -5
T 5
S B
T -5
T A
S F
*/