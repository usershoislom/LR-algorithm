#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <stack>
#include <map>

class LR {
 private:
  class Automaton;
  struct State;

 public:
  class Grammar;
  LR() = default;

  class Grammar {
   public:

    Grammar() = default;

    Grammar(std::unordered_set<char> terminals, std::unordered_set<char> non_terminals)
        : terminals(std::move(terminals)), non_terminals(std::move(non_terminals)) {
    }

    void InsertRule(const std::string &rule) {
      if (rule.size() <= 3) {
        states.emplace_back(rule.substr(0, 1), "");
      }
      states.emplace_back(rule.substr(0, 1), rule.substr(3, rule.size() - 3));
    }

    void SetStart(std::string start) {
      states.emplace_back("#", std::move(start));
      start_state = &states.back();
      non_terminals.insert('#');
    }

    const State &GetStart() {
      return *start_state;
    }

    const std::vector<State> &GetStates() {
      return states;
    }

    const std::unordered_set<char> &GetTerminals() {
      return terminals;
    }

   private:
    std::vector<State> states;
    std::unordered_set<char> terminals;
    std::unordered_set<char> non_terminals;
    State *start_state = nullptr;
  };

  void Fit(Grammar G);
  bool Predict(const std::string &word);

 private:

  class bad_grammar_exception : public std::runtime_error {
   public:
    bad_grammar_exception() : std::runtime_error("Input grammar is not LR(1)-grammar") {
    }
  };

  struct State {
   public:

    State() = default;

    State(std::string rule_name, std::string rule, size_t index = 0, char predicted = '$') : str_state(
        rule_name + rule), rule_name(std::move(rule_name)), rule(std::move(rule)), index(index), predicted(predicted) {
    }

    bool operator==(const State &other) const {
      return index == other.index && predicted == other.predicted && rule == other.rule && rule_name == other.rule_name;
    }

    bool operator!=(const State &other) const {
      return !(*this == other);
    }

    std::string str_state;
    std::string rule_name;
    std::string rule;
    int64_t index = 0;
    char predicted = '$';
  };

  struct StateHasher {
    size_t operator()(const State &state) const {
      return std::hash<std::string>()(state.str_state);
    }
  };

  class Automaton {

   public:

    Automaton() = default;

    explicit Automaton(Grammar grammar) : grammar(std::move(grammar)) {

    }

    void Build(const State &start_state) {
      Node start;
      start.states.emplace(start_state.rule_name,
                           start_state.rule);
      ProcessNode(start);
      nodes.insert(start);
      for (auto &node : nodes) {
        Node &node_to_change = const_cast<Node &>(node);
        for (auto &edge : node_to_change.edges) {
          node_to_change.real_edges[edge.first] = &*nodes.find(edge.second);
        }
      }
      processed.clear();
      lr_table =
          std::vector<std::unordered_map<char, std::pair<std::string, int64_t>>>(nodes.size());
      EnumerateNodes();
      term_node = node_to_number[nodes.find(start)->edges.find(start_state.rule[0])->second];
      start_node = node_to_number[(*nodes.find(start))];
      BuildTable(start_node);
    }

    bool Predict(std::string word) {
      word.push_back('$');
      std::stack<char> char_stack;
      std::stack<int64_t> node_stack;
      int64_t cur = start_node;
      node_stack.push(cur);
      for (uint64_t i = 0; i < word.size(); ++i) {
        if (lr_table[cur].count(word[i]) == 0) {
          return false;
        } else {
          auto[op, act] = lr_table[cur][word[i]];
          if (op == "S") {
            cur = act;
            char_stack.push(word[i]);
            node_stack.push(cur);
          } else if (op[0] == 'R') {
            for (int64_t counter = 0; counter < act; ++counter) {
              node_stack.pop();
              char_stack.pop();
              cur = node_stack.top();
            }
            char_stack.push(op[1]);
            cur = lr_table[cur][op[1]].second;
            node_stack.push(cur);
            if (i == word.size() - 1 && cur == term_node) {
              return true;
            }
            --i;
          }
        }
      }
      if (cur == term_node) {
        return true;
      } else {
        return false;
      }
    }

   private:

    struct Node {
     public:
      bool operator==(const Node &other) const {
        return other.states == states;
      }

      bool operator!=(const Node &other) const {
        return !(*this == other);
      }

      std::unordered_set<State, StateHasher> states;
      std::map<char, Node> edges;
      std::unordered_map<char, const Node *> real_edges;
    };

    struct NodeHasher {
      size_t operator()(const Node &node) const {
        size_t hash = 0;
        for (const auto &state : node.states) {
          hash += StateHasher()(state);
        }
        return hash;
      };
    };

    std::unordered_set<char> ProcessClosestTerminals(const State &current_rule,
                                                     std::unordered_set<State, StateHasher> &being_processed) {
      if (being_processed.count(current_rule) != 0) {
        return {};
      }
      if (current_rule.rule.empty()) {
        return {'$'};
      } else if (grammar.GetTerminals().count(current_rule.rule[current_rule.index]) != 0) {
        return {current_rule.rule[current_rule.index]};
      } else {
        being_processed.insert(current_rule);
        std::unordered_set<char> closest_terms;
        for (const auto &gr_rule : grammar.GetStates()) {
          if (current_rule.rule[current_rule.index] == gr_rule.rule_name[0]) {
            if (gr_rule.rule.empty() || grammar.GetTerminals().count(current_rule.rule[current_rule.index]) != 0) {
              closest_terms.insert(gr_rule.rule.empty() ? '$' : current_rule.rule[current_rule.index]);
            } else if (gr_rule != current_rule) {
              std::unordered_set<char>
                  gr_terms = ProcessClosestTerminals(State(gr_rule.rule_name, gr_rule.rule), being_processed);
              for (const auto &c : gr_terms) {
                closest_terms.insert(c);
              }
            }
          }
        }
        if (closest_terms.count('$') != 0 && current_rule.index + 1 != current_rule.rule.size()) {
          for (const auto &c : ProcessClosestTerminals(State(current_rule.rule_name,
                                                             current_rule.rule,
                                                             current_rule.index + 1), being_processed)) {
            closest_terms.erase('$');
            closest_terms.insert('$');
          }
        }
        being_processed.erase(current_rule);
        return closest_terms;
      }
    }

    void ProcessNode(Node &to_process) {
      bool changed = true;
      std::unordered_map<char, Node> new_edges;
      while (changed) {
        changed = false;
        std::unordered_set<State, StateHasher> copy_states = to_process.states;
        for (const auto &state : copy_states) {
          for (const auto &gr_rule : grammar.GetStates()) {
            if (state.index != state.rule.size()) {
              State next_node_state = state;
              ++next_node_state.index;
              new_edges[state.rule[state.index]].states.insert(next_node_state);
              if (state.rule[state.index] == gr_rule.rule_name[0]) {
                State new_state = gr_rule;
                if (state.index + 1 != state.rule.size()) {
                  if (grammar.GetTerminals().count(state.rule[state.index + 1]) != 0) {
                    new_state.predicted = state.rule[state.index + 1];
                  } else {
                    std::unordered_set<State, StateHasher> being_processed;
                    std::unordered_set<char>
                        closest_terms =
                        ProcessClosestTerminals(State(state.rule_name, state.rule, state.index + 1), being_processed);
                    for (char c : closest_terms) {
                      if (c == '$') {
                        new_state.predicted = state.predicted;
                      } else {
                        new_state.predicted = c;
                      }
                    }
                  }
                } else {
                  new_state.predicted = state.predicted;
                }
                auto[it, res] = to_process.states.insert(new_state);
                changed |= res;
              }
            }
          }
        }
      }
      if (processed.count(to_process) == 0) {
        processed.insert(to_process);
        for (auto &new_node : new_edges) {
          ProcessNode(new_node.second);
          to_process.edges.emplace(new_node.first, new_node.second);
        }
        processed.erase(to_process);
        processed.insert(to_process);
        nodes.insert(to_process);
      }
    }

    void EnumerateNodes() {
      number_to_node = std::vector<Node>(nodes.size());
      int64_t counter = 0;
      for (const auto &node: nodes) {
        number_to_node[counter] = node;
        node_to_number[node] = counter;
        ++counter;
      }
    }

    void BuildTable(const int64_t current_node) {
      if (built.count(current_node) != 0) {
        return;
      }
      built.insert(current_node);
      for (const auto &state : number_to_node[current_node].states) {
        if (state.index == state.rule.size()) {
          if (lr_table[current_node].count(state.predicted) != 0) {
            throw bad_grammar_exception();
          }
          lr_table[current_node][state.predicted] = {"R" + state.rule_name, state.rule.size()};
        }
      }
      for (const auto &edge : number_to_node[current_node].real_edges) {
        if (lr_table[current_node].count(edge.first) != 0) {
          throw bad_grammar_exception();
        }
        lr_table[current_node][edge.first] = {"S", node_to_number[*edge.second]};
        BuildTable(node_to_number[*edge.second]);
      }
    }

    std::unordered_set<Node, NodeHasher> nodes;
    Grammar grammar;
    std::unordered_set<Node, NodeHasher> processed;
    std::unordered_set<int64_t> built;
    std::vector<std::unordered_map<char, std::pair<std::string, int64_t>>> lr_table;
    std::unordered_map<Node, int64_t, NodeHasher> node_to_number;
    std::vector<Node> number_to_node;
    int64_t start_node = -1;
    int64_t term_node = -1;
  };

  Automaton LR_automaton;

};

void LR::Fit(Grammar G) {
  LR_automaton = Automaton(G);
  LR_automaton.Build(G.GetStart());
}

bool LR::Predict(const std::string &word) {
  return LR_automaton.Predict(word);
}

int main() {
  std::cout << "Insert amount of not-term symbols, amount of term-symbols and amount of rules in your grammar:\n";
  int64_t non_term_amount;
  int64_t term_amount;
  int64_t rules_amount;
  std::cin >> non_term_amount >> term_amount >> rules_amount;
  std::cout << "Insert non-terminal symbols:\n";
  std::string non_term_symbols;
  std::cin >> non_term_symbols;
  std::unordered_set<char> non_terms_set;
  for (char c : non_term_symbols) {
    non_terms_set.insert(c);
  }
  std::cout << "Insert terminal symbols:\n";
  std::string term_symbols;
  std::cin >> term_symbols;
  std::unordered_set<char> terms_set;
  for (char c : term_symbols) {
    terms_set.insert(c);
  }
  std::cout << "Insert your grammar:\n";
  std::string new_rule;
  LR::Grammar grammar(terms_set, non_terms_set);
  for (int64_t i = 0; i < rules_amount; ++i) {
    std::cin >> new_rule;
    grammar.InsertRule(new_rule);
  }
  std::string start;
  std::cout << "Insert start rule:\n";
  std::cin >> start;
  grammar.SetStart(start);
  LR parser;
  parser.Fit(grammar);
  std::cout << "Insert amount of words:\n";
  int64_t words_amount;
  std::cin >> words_amount;
  std::cout << "Insert your words:\n";
  std::string word;
  std::getline(std::cin, word);
  for (int64_t i = 0; i < words_amount; ++i) {
    std::getline(std::cin, word);
    std::cout << (parser.Predict(word) ? "Yes\n" : "No\n");
  }
  return 0;
}
