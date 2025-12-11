# Compilation

```
g++ -O3 -std=c++17 -o indian_poker_solver indian_poker_solver.cpp
g++ -O3 -std=c++17 -o auction_poker_solver auction_poker_solver.cpp
g++ -O3 -std=c++17 -o auction_poker_deep_cfr auction_poker_deep_cfr.cpp
```

# Run Example

```
./indian_poker_solver --time_ms 1000 --seed 42
./auction_poker_solver --time_ms 100 --seed 42 --eval 400
./auction_poker_deep_cfr --time_ms 100 --seed 42 --eval 400
```
