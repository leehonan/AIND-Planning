from aimacode.logic import PropKB
from aimacode.planning import Action
from aimacode.search import (
    Node, Problem,
)
from aimacode.utils import expr
from lp_utils import (
    FluentState, encode_state, decode_state,
)
from my_planning_graph import PlanningGraph

from functools import lru_cache

from collections import Counter


class AirCargoProblem(Problem):

    def __init__(self, cargos, planes, airports, initial: FluentState, goal: list):
        """

        :param cargos: list of str
            cargos in the problem
        :param planes: list of str
            planes in the problem
        :param airports: list of str
            airports in the problem
        :param initial: FluentState object
            positive and negative literal fluents (as expr) describing initial state
        :param goal: list of expr
            literal fluents required for goal test
        """
        self.state_map = initial.pos + initial.neg
        self.initial_state_TF = encode_state(initial, self.state_map)
        Problem.__init__(self, self.initial_state_TF, goal=goal)
        self.cargos = cargos
        self.planes = planes
        self.airports = airports
        self.actions_list = self.get_actions()


    def get_actions(self):
        """
        This method creates concrete actions (no variables) for all actions in the problem
        domain action schema and turns them into complete Action objects as defined in the
        aimacode.planning module. It is computationally expensive to call this method directly;
        however, it is called in the constructor and the results cached in the `actions_list` property.

        Returns:
        ----------
        list<Action>
            list of Action objects
        """

        # TODO create concrete Action objects based on the domain action schema for: Load, Unload, and Fly
        # concrete actions definition: specific literal action that does not include variables as with the schema
        # for example, the action schema 'Load(c, p, a)' can represent the concrete actions 'Load(C1, P1, SFO)'
        # or 'Load(C2, P2, JFK)'.  The actions for the planning problem must be concrete because the problems in
        # forward search and Planning Graphs must use Propositional Logic


        def load_actions():
            """Create all concrete Load actions and return a list

            :return: list of Action objects
            """
            # TODO create all load ground actions from the domain Load action
            '''
                PDDL:
                    Action(Load(c, p, a),
	                    PRECOND: At(c, a) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
	                    EFFECT: ¬ At(c, a) ∧ In(c, p))
            '''
            # list of load action objects
            loads = []

            # iterate through each airport/plane/cargo combination and generate a Load Action
            # object for each possible combination
            for airport in self.airports:
                for plane in self.planes:
                    for cargo in self.cargos:
                        # initialise positive preconditions
                        precond_pos = [expr("At({}, {})".format(cargo, airport)),
                                            expr("At({}, {})".format(plane, airport))]
                        # no need to initialise negative preconditions
                        precond_neg = []

                        # load action removes cargo from airport (- at) and places it on plane (+
                        #  in)
                        effect_rem = [expr("At({}, {})".format(cargo, airport))]
                        effect_add = [expr("In({}, {})".format(cargo, plane))]

                        # instantiate Action object and add to list
                        load = Action(action=expr("Load({}, {}, {})".format(cargo, plane, airport)),
                                     precond=[precond_pos, precond_neg],
                                     effect=[effect_add, effect_rem])
                        loads.append(load)
            return loads

        def unload_actions():
            """Create all concrete Unload actions and return a list

            :return: list of Action objects
            """
            # TODO create all Unload ground actions from the domain Unload action
            '''
                PDDL:
                    Action(Unload(c, p, a),
                        PRECOND: In(c, p) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
                        EFFECT: At(c, a) ∧ ¬ In(c, p))
            '''
            # list of unload action objects
            unloads = []

            # iterate through each airport/plane/cargo combination and generate an Unload Action
            # object for each possible combination

            for airport in self.airports:
                for plane in self.planes:
                    for cargo in self.cargos:
                        # initialise positive preconditions
                        precond_pos = [expr("In({}, {})".format(cargo, plane)),
                                        expr("At({}, {})".format(plane, airport))]
                        # no need to initialise negative preconditions
                        precond_neg = []

                        # unload action removes cargo from plane (- in) and deposits it at airport
                        # (+ at)
                        effect_rem = [expr("In({}, {})".format(cargo, plane))]
                        effect_add = [expr("At({}, {})".format(cargo, airport))]

                        # instantiate Action object and add to list
                        unload = Action(action=expr("Unload({}, {}, {})".format(cargo, plane,
                                                                             airport)),
                                     precond=[precond_pos, precond_neg],
                                     effect=[effect_add, effect_rem])
                        unloads.append(unload)
            return unloads


        def fly_actions():
            """Create all concrete Fly actions and return a list

            :return: list of Action objects
            """

            '''
                PDDL:
                    Action(Fly(p, from, to),
	                    PRECOND: At(p, from) ∧ Plane(p) ∧ Airport(from) ∧ Airport(to)
	                    EFFECT: ¬ At(p, from) ∧ At(p, to))
            '''
            # list of fly action objects
            flys = []

            # iterate through airport/plane combinations and generate fly actions for each (
            # ensuring from != to)
            for airport_from in self.airports:
                for airport_to in [airport_to for airport_to in self.airports if airport_to != airport_from]:
                    for plane in self.planes:
                        # initialise positive preconditions
                        precond_pos = [expr("At({}, {})".format(plane, airport_from))]
                        # no need to initialise negative preconditions
                        precond_neg = []

                        # fly action removes plane from airport_from (- at) and transitions it to
                        #  airport_to (+ at)
                        effect_rem = [expr("At({}, {})".format(plane, airport_from))]
                        effect_add = [expr("At({}, {})".format(plane, airport_to))]

                        # instantiate Action object and add to list
                        fly = Action(action=expr("Fly({}, {}, {})".format(plane, airport_from,
                                                                   airport_to)),
                                     precond=[precond_pos, precond_neg],
                                     effect=[effect_add, effect_rem])
                        flys.append(fly)
            return flys

        return load_actions() + unload_actions() + fly_actions()


    def actions(self, state: str) -> list:
        """ Return the actions that can be executed in the given state.

        :param state: str
            state represented as T/F string of mapped fluents (state variables)
            e.g. 'FTTTFF'
        :return: list of Action objects
        """
        # TODO implement

        # return list of allowable actions
        possible_actions = []

        # instantiate propositional knowledge base to test whether each action is valid
        # for the current state of the world
        knowledge_base = PropKB()
        knowledge_base.tell(sentence=decode_state(state, self.state_map).pos_sentence())

        # test each action's precondition clauses for validity against the KB's SOTW
        for action in self.actions_list:
            # action will be invalid if a single assertion fails
            is_action_ok = True
            # find invalid pos clauses - precond does not exist in SOTW
            for precond_pos_clause in [clause for clause in action.precond_pos if clause not in
                                            knowledge_base.clauses]:
                is_action_ok = False
                break
            # find invalid neg clauses - negative precond exists in SOTW
            if is_action_ok:
                for precond_neg_clause in [clause for clause in action.precond_neg if clause in
                                            knowledge_base.clauses]:
                    is_action_ok = False
                    break

            if is_action_ok:
                possible_actions.append(action)

        return possible_actions


    def result(self, state: str, action: Action):
        """ Return the state that results from executing the given
        action in the given state. The action must be one of
        self.actions(state).

        :param state: state entering node
        :param action: Action applied
        :return: resulting state after action
        """
        # TODO implement
        # initialise empty fluent for to-be state and get string rep for as-is state
        new_state = FluentState([], [])
        old_state = decode_state(state=state, fluent_map=self.state_map)

        # carry over positive fluents from the old state where not negative given action effect
        for fluent in [fluent for fluent in old_state.pos if fluent not in action.effect_rem]:
            new_state.pos.append(fluent)

        # carry over negative fluents from the old state where not positive given action effect
        for fluent in [fluent for fluent in old_state.neg if fluent not in action.effect_add]:
            new_state.neg.append(fluent)

        # add new positive fluents given action effect
        for fluent in [fluent for fluent in action.effect_add if fluent not in new_state.pos]:
            new_state.pos.append(fluent)

        # add new negative fluents given action effect
        for fluent in [fluent for fluent in action.effect_rem if fluent not in new_state.neg]:
            new_state.neg.append(fluent)

        # re-encode new state, return
        return encode_state(fs=new_state, fluent_map=self.state_map)


    def goal_test(self, state: str) -> bool:
        """ Test the state to see if goal is reached

        :param state: str representing state
        :return: bool
        """
        knowledge_base = PropKB()
        knowledge_base.tell(sentence=decode_state(state, self.state_map).pos_sentence())
        for clause in self.goal:
            if clause not in knowledge_base.clauses:
                return False
        return True


    def h_1(self, node: Node):
        # note that this is not a true heuristic
        h_const = 1
        return h_const


    @lru_cache(maxsize=8192)
    def h_pg_levelsum(self, node: Node):
        """This heuristic uses a planning graph representation of the problem
        state space to estimate the sum of all actions that must be carried
        out from the current state in order to satisfy each individual goal
        condition.
        """
        # requires implemented PlanningGraph class
        pg = PlanningGraph(self, node.state)
        pg_levelsum = pg.h_levelsum()
        return pg_levelsum


    @lru_cache(maxsize=8192)
    def h_ignore_preconditions(self, node: Node):
        """This heuristic estimates the minimum number of actions that must be
        carried out from the current state in order to satisfy all of the goal
        conditions by ignoring the preconditions required for an action to be
        executed.
        """
        # TODO implement (see Russell-Norvig Ed-3 10.2.3  or Russell-Norvig Ed-2 11.2)

        # I am taking the assumption (per forums - SHOULD BE IN DOCSTRING ABOVE!!!) that there is
        # a one-to-one relationship between an unmet goal and an action, as opposed to the
        # statement in the AIMA text that one should consider that "some action may achieve
        # multiple goals"

        knowledge_base = PropKB()
        num_goals = len(self.goal)
        knowledge_base.tell(sentence=decode_state(node.state, self.state_map).pos_sentence())

        # count goals that have already been achieved - could have just used goal_test()
        goal_met_count = Counter([clause for clause in self.goal if clause in
                                            knowledge_base.clauses])

        # minimum number of actions is number of remaining goals
        return num_goals - sum(goal_met_count.values())


def air_cargo_p1() -> AirCargoProblem:
    '''
    Problem 1 initial state and goal:

    Init(At(C1, SFO) ∧ At(C2, JFK)
        ∧ At(P1, SFO) ∧ At(P2, JFK)
        ∧ Cargo(C1) ∧ Cargo(C2)
        ∧ Plane(P1) ∧ Plane(P2)
        ∧ Airport(JFK) ∧ Airport(SFO))
    Goal(At(C1, JFK) ∧ At(C2, SFO))
    '''
    cargos = ['C1', 'C2']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO']

    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)')]

    neg = [expr('At(C2, SFO)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),
           expr('At(C1, JFK)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),
           expr('At(P1, JFK)'),
           expr('At(P2, SFO)')]

    # set initial state as fluent of positive and negative assertions
    init = FluentState(pos_list=pos, neg_list=neg)

    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)')]

    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p2() -> AirCargoProblem:
    '''
    Problem 2 initial state and goal:
    Init(At(C1, SFO) ∧ At(C2, JFK) ∧ At(C3, ATL)
        ∧ At(P1, SFO) ∧ At(P2, JFK) ∧ At(P3, ATL)
        ∧ Cargo(C1) ∧ Cargo(C2) ∧ Cargo(C3)
        ∧ Plane(P1) ∧ Plane(P2) ∧ Plane(P3)
        ∧ Airport(JFK) ∧ Airport(SFO) ∧ Airport(ATL))
    Goal(At(C1, JFK) ∧ At(C2, SFO) ∧ At(C3, SFO))
    '''
    cargos = ['C1', 'C2', 'C3']
    planes = ['P1', 'P2', 'P3']
    airports = ['JFK', 'SFO', 'ATL']

    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(C3, ATL)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           expr('At(P3, ATL)')]

    neg = [expr('At(C1, JFK)'),     # C1 at SFO
           expr('At(C1, ATL)'),
           expr('In(C1, P1)'),      # Cargo is not loaded
           expr('In(C1, P2)'),
           expr('In(C1, P3)'),
           expr('At(C2, SFO)'),     # C2 at JFK
           expr('At(C2, ATL)'),
           expr('In(C2, P1)'),      # Cargo is not loaded
           expr('In(C2, P2)'),
           expr('In(C2, P3)'),
           expr('At(C3, SFO)'),     # C3 at ATL
           expr('At(C3, JFK)'),
           expr('In(C3, P1)'),      # Cargo is not loaded
           expr('In(C3, P2)'),
           expr('In(C3, P3)'),
           expr('At(P1, JFK)'),     # P1 at SFO
           expr('At(P1, ATL)'),
           expr('At(P2, SFO)'),     # P2 at JFK
           expr('At(P2, ATL)'),
           expr('At(P3, SFO)'),     # P3 at ATL
           expr('At(P3, JFK)')]

    # set initial state as fluent of positive and negative assertions
    init = FluentState(pos_list=pos, neg_list=neg)

    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            expr('At(C3, SFO)')]

    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p3() -> AirCargoProblem:
    '''
    Problem 3 initial state and goal:

    Init(At(C1, SFO) ∧ At(C2, JFK) ∧ At(C3, ATL) ∧ At(C4, ORD)
        ∧ At(P1, SFO) ∧ At(P2, JFK)
        ∧ Cargo(C1) ∧ Cargo(C2) ∧ Cargo(C3) ∧ Cargo(C4)
        ∧ Plane(P1) ∧ Plane(P2)
        ∧ Airport(JFK) ∧ Airport(SFO) ∧ Airport(ATL) ∧ Airport(ORD))
    Goal(At(C1, JFK) ∧ At(C3, JFK) ∧ At(C2, SFO) ∧ At(C4, SFO))
    '''
    cargos = ['C1', 'C2', 'C3', 'C4']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO', 'ATL', 'ORD']

    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(C3, ATL)'),
           expr('At(C4, ORD)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)')]

    neg = [expr('At(C1, JFK)'),     # C1 at SFO
           expr('At(C1, ATL)'),
           expr('At(C1, ORD)'),
           expr('In(C1, P1)'),      # Cargo is not loaded
           expr('In(C1, P2)'),
           expr('At(C2, SFO)'),     # C2 at JFK
           expr('At(C2, ATL)'),
           expr('At(C2, ORD)'),
           expr('In(C2, P1)'),      # Cargo is not loaded
           expr('In(C2, P2)'),
           expr('At(C3, SFO)'),     # C3 at ATL
           expr('At(C3, JFK)'),
           expr('At(C3, ORD)'),
           expr('In(C3, P1)'),      # Cargo is not loaded
           expr('In(C3, P2)'),
           expr('At(C4, SFO)'),     # C4 at ORD
           expr('At(C4, JFK)'),
           expr('At(C4, ATL)'),
           expr('In(C4, P1)'),      # Cargo is not loaded
           expr('In(C4, P2)'),
           expr('At(P1, JFK)'),     # P1 at SFO
           expr('At(P1, ATL)'),
           expr('At(P1, ORD)'),
           expr('At(P2, SFO)'),     # P2 at JFK
           expr('At(P2, ATL)'),
           expr('At(P2, ORD)')]

    # set initial state as fluent of positive and negative assertions
    init = FluentState(pos_list=pos, neg_list=neg)
    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            expr('At(C3, JFK)'),
            expr('At(C4, SFO)')]

    return AirCargoProblem(cargos, planes, airports, init, goal)


def main():
    '''
    For debugging
    '''
    print('=====  AIR CARGO PLANNER PDDL TEST  =====\n')
    problem = air_cargo_p1()

    print('Initial Fluent States:')
    for i, fluent in enumerate(problem.state_map):
        print('    {}: {}'.format(str(fluent), problem.initial[i]))

    print('Actions:')
    for action in problem.actions_list:
        print('    {}: {}'.format(action.name, action.args))

    print('Goals:')
    for goal in problem.goal:
        print('    {}'.format(goal))


if __name__== '__main__':
    main()
