import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """

        #
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """

        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []


    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        def remove_fact_rule(fact_or_rule):
            print("一次递归开始+++++++")
            if fact_or_rule.asserted == True:
                print("end!!!! 此时fact_or_rule.asserted为true,直接结束")
                return

            if len(fact_or_rule.supported_by) >= 2:
                print("end!!!! 此时fact_or_rule.supported_by的长度大于2,直接结束")
                return

            if len(fact_or_rule.supports_rules) == 0 and len(fact_or_rule.supports_facts) == 0:
                print("end!!!! 此时fact_or_rule的supports_rules和supports_facts的长度都是为0,删除自己后直接结束")
                if isinstance(fact_or_rule, Fact):
                    self.facts.remove(fact_or_rule)
                    return
                else:
                    self.rules.remove(fact_or_rule)
                    return

            print("len(fact_or_rule.supports_facts):{", len(fact_or_rule.supports_facts))
            print("len(fact_or_rule.supports_rules):{", len(fact_or_rule.supports_rules))

            if isinstance(fact_or_rule, Fact):
                if len(fact_or_rule.supports_facts) != 0:
                    new_supports_facts =[]
                    for item_fact in fact_or_rule.supports_facts:
                        new_supports_facts.append(item_fact)
                    fact_or_rule.supports_facts = []

                    for item_fact in new_supports_facts:
                        # 移除自身对应的支持的fact
                        print("len(item_fact.supports_facts):[", len(item_fact.supports_facts))
                        print("len(item_fact.supports_rules):[", len(item_fact.supports_rules))
                        index = item_fact.supported_by.index(fact_or_rule)
                        pair_rule = item_fact.supported_by[index+1]
                        # 找到同时支持的配对的rule,同样也删除支持物
                        pair_rule.supports_facts.remove(item_fact)
                        item_fact.supported_by.remove(fact_or_rule)
                        item_fact.supported_by.remove(pair_rule)
                        # 就是我上一个的支持的fact,的两翼给清空了, 此时,应该放入递归中进行继续循环的
                        remove_fact_rule(item_fact)
                if len(fact_or_rule.supports_rules) != 0:
                    print("supports_rules的长度不为0,所以,才进行循环的")

                    new_supports_rules =[]
                    for item_rule in fact_or_rule.supports_rules:
                        new_supports_rules.append(item_rule)
                    fact_or_rule.supports_rules = []

                    for item_rule in new_supports_rules:
                        # 就是遍历自己的规则部分, 然后遍历出来之后删除掉的
                        index = item_rule.supported_by.index(fact_or_rule)
                        pair_rule = item_rule.supported_by[index+1]
                        # 然后,就找到配对的这个rule的,然后进行移除操作的
                        pair_rule.supports_rules.remove(item_rule)
                        item_rule.supported_by.remove(fact_or_rule)
                        item_rule.supported_by.remove(pair_rule)
                        # 同样的道理,我找到这个supports_rules之后,把这个rules给全部清空的,
                        # 清空之后,这个下一个同样也要进行清空的操作的
                        remove_fact_rule(item_rule)
            if isinstance(fact_or_rule, Rule):
                # 该部分就是rule的了,注意这个前面减去1就可以了

                if len(fact_or_rule.supports_facts) != 0:

                    new_supports_facts =[]
                    for item_fact in fact_or_rule.supports_facts:
                        new_supports_facts.append(item_fact)
                    fact_or_rule.supports_facts = []

                    for item_fact in new_supports_facts:
                        # 移除自身对应的支持的fact
                        index = item_fact.supported_by.index(fact_or_rule)
                        pair_fact = item_fact.supported_by[index-1]
                        # 找到同时支持的配对的rule,同样也删除支持物
                        pair_fact.supports_facts.remove(item_fact)
                        item_fact.supported_by.remove(fact_or_rule)
                        item_fact.supported_by.remove(pair_fact)
                        # 就是我上一个的支持的fact,的两翼给清空了, 此时,应该放入递归中进行继续循环的
                        remove_fact_rule(item_fact)
                if len(fact_or_rule.supports_rules) != 0:

                    new_supports_rules = []
                    for item_rule in fact_or_rule.supports_rules:
                        new_supports_rules.append(item_rule)
                    fact_or_rule.supports_rules = []

                    for item_rule in new_supports_rules:
                        # 就是遍历自己的规则部分, 然后遍历出来之后删除掉的
                        index = item_rule.supported_by.index(fact_or_rule)
                        pair_fact = item_rule.supported_by[index-1]
                        # 然后,就找到配对的这个rule的,然后进行移除操作的
                        pair_fact.supports_rules.remove(item_rule)
                        item_rule.supported_by.remove(fact_or_rule)
                        item_rule.supported_by.remove(pair_fact)
                        # 同样的道理,我找到这个supports_rules之后,把这个rules给全部清空的,
                        # 清空之后,这个下一个同样也要进行清空的操作的
                        remove_fact_rule(item_rule)

            print("这是递归的最后完成之后,自己要删除自己的,因为前面的任务已经完成的了")
            if isinstance(fact_or_rule, Fact):
                self.facts.remove(fact_or_rule)
                print("这个是要真正的移除,如果移除完成则会进行打印的, 但是里面就是直接结束了,压根就没有什么递归调用的")
            else:
                self.rules.remove(fact_or_rule)

        print("kb_retract方法已经被调用")
        if isinstance(fact_or_rule, Fact):
            # print(fact_or_rule.__str__())
            if fact_or_rule.asserted == True:
                fact_or_rule1 = self._get_fact(fact_or_rule)
                print("len(fact_or_rule1.supports_facts):", len(fact_or_rule1.supports_facts))
                print("len(fact_or_rule1.supports_rules):", len(fact_or_rule1.supports_rules))
                if len(fact_or_rule1.supported_by) >= 2:
                    fact_or_rule1.asserted = False
                else:
                    fact_or_rule1.asserted = False
                    print("kb_retract中的asserted赋值为false,然后继续进行删除的")
                    print("-----------进入递归--------------------")
                    remove_fact_rule(fact_or_rule1)




class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        if len(rule.lhs) == 0:
            return

        bindings = match(fact.statement, rule.lhs[0])
        if bindings:
            if len(rule.lhs) == 1:
                    new_fact = Fact(instantiate(rule.rhs, bindings), [fact, rule])
                    fact.supports_facts.append(new_fact)
                    rule.supports_facts.append(new_fact)
                    kb.kb_assert(new_fact)
            else:
                new_rule_lhs = []
                for item in rule.lhs[1:]:
                    new_rule_lhs.append(instantiate(item, bindings))
                new_rule = Rule([new_rule_lhs, instantiate(rule.rhs, bindings)], [fact, rule])
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                kb.kb_assert(new_rule)

        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
