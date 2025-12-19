import os
import sys
import time
# import pandas as pd
import numpy as np
# from numpy import number
# from numpy.lib.user_array import container
import random
# import copy
import csv
import MSCRB_Model as M
# import subprocess
from collections import defaultdict
import cProfile
import itertools
import gurobipy as gp
from gurobipy import GRB, Model
import math
import re


class MSCRBSolution:
    def __init__(self, MSCRBProblem, allocated_jobs=None, name="Main"):
        self.MSCRBProblem = MSCRBProblem
        if allocated_jobs is None:
            # one empty list per SC
            self.allocated_jobs = [[] for _ in range(len(MSCRBProblem.scs))]
        else:
            # assume caller passes correct structure
            self.allocated_jobs = allocated_jobs
        self.objective_function = sys.maxsize  # The current objective function
        self.name = name
        self.gurobi_time = None
        self.gurobi_gap = None
        self.gurobi_status = None

    def print_allocations(self):
        for x in self.allocated_jobs:
            print("[", end=" ")
            if x is not None:
                for c in x:
                    print(c.name + c.kind, end=" ")
            print("]")

    def copy_allocated_jobs(self):
        new_list = []
        for inner_list in self.allocated_jobs:
            new_inner_list = []  # copy.copy(inner_list) # Shallow copy of the inner list to preserve original objects
            for object in inner_list:
                new_inner_list.append(object)
            # new_inner_list = copy.copy(inner_list)
            new_list.append(new_inner_list)
        return new_list

    def Gurobi(self):

        m = gp.Model("SCsRoutingOOP")

        x = m.addVars(self.MSCRBProblem.A, vtype=GRB.BINARY, name="x")

        win = m.addVars(self.MSCRBProblem.AllContbufint, lb=0, vtype=GRB.INTEGER, name="win")
        wout = m.addVars(self.MSCRBProblem.AllContbufint, lb=0, vtype=GRB.INTEGER, name="wout")

        w = m.addVars(self.MSCRBProblem.R, lb=0, vtype=GRB.INTEGER, name="w")

        bin = m.addVars(self.MSCRBProblem.forbin, vtype=GRB.BINARY, name="bin")
        bout = m.addVars(self.MSCRBProblem.forout, vtype=GRB.BINARY, name="bout")

        start = m.addVars(self.MSCRBProblem.J + self.MSCRBProblem.R + self.MSCRBProblem.scs, vtype=GRB.INTEGER,
                          name="start")
        end = m.addVars(self.MSCRBProblem.J + self.MSCRBProblem.R + self.MSCRBProblem.scs, vtype=GRB.INTEGER,
                        name="end")
        stack = m.addVars(self.MSCRBProblem.J + self.MSCRBProblem.R + self.MSCRBProblem.scs, vtype=GRB.INTEGER,
                          name="stack")

        m.addConstrs((win[j] - self.MSCRBProblem.tjob[j] == start[j] for j in self.MSCRBProblem.Jl),
                     name="loadingstart")
        m.addConstrs((end[j] == win[j] for j in self.MSCRBProblem.Jl), name="loadingend")
        m.addConstrs(
            (win[j] - self.MSCRBProblem.tjob[j] + self.MSCRBProblem.tv == stack[j] for j in self.MSCRBProblem.Jl),
            name="loadingstack")

        m.addConstrs((wout[j] == start[j] for j in self.MSCRBProblem.Ju), name="unloadingstart")
        m.addConstrs((wout[j] + self.MSCRBProblem.tjob[j] == end[j] for j in self.MSCRBProblem.Ju), name="unloadingend")
        m.addConstrs((wout[j] + self.MSCRBProblem.tjob[j] == stack[j] for j in self.MSCRBProblem.Ju),
                     name="unloadingstack")

        m.addConstrs((w[j] == start[j] for j in self.MSCRBProblem.R), name="restackingstart")
        m.addConstrs((w[j] + self.MSCRBProblem.tjob[j] == end[j] for j in self.MSCRBProblem.R), name="restackingend")
        m.addConstrs((w[j] + self.MSCRBProblem.tv == stack[j] for j in self.MSCRBProblem.R), name="restackingstack")

        m.addConstrs((end[j] == j.avl for j in self.MSCRBProblem.scs), name="scend")

        m.addConstrs((gp.quicksum(
            x[self.MSCRBProblem.A[i][0], self.MSCRBProblem.A[i][1]] for i in range(0, len(self.MSCRBProblem.A)) if
            self.MSCRBProblem.A[i][1] == j) == 1 for j in self.MSCRBProblem.J + self.MSCRBProblem.R), name="Cons5")

        m.addConstrs((gp.quicksum(
            x[self.MSCRBProblem.A[i][0], self.MSCRBProblem.A[i][1]] for i in range(0, len(self.MSCRBProblem.A)) if
            self.MSCRBProblem.A[i][0] == j) <= 1 for j in
                      self.MSCRBProblem.J + self.MSCRBProblem.R + self.MSCRBProblem.scs),
                     name="Cons6")

        m.addConstrs((end[self.MSCRBProblem.A[i][0]] + self.MSCRBProblem.Tunloaded[self.MSCRBProblem.A[i][0]][
            self.MSCRBProblem.A[i][1]] - start[self.MSCRBProblem.A[i][1]] <= (
                              1 - x[self.MSCRBProblem.A[i][0], self.MSCRBProblem.A[i][1]]) * self.MSCRBProblem.M for i
                      in
                      range(len(self.MSCRBProblem.A))), name="Cons7")

        m.addConstrs(
            (wout[self.MSCRBProblem.Jc[a][i]] + self.MSCRBProblem.tq - wout[self.MSCRBProblem.Jc[a][i + 1]] <= 0 for a
             in
             self.MSCRBProblem.LoadingCranes for i in range(len(self.MSCRBProblem.Jc[a]) - 1)),
            name="Cons8LoadingCrane")
        m.addConstrs((-80 + 80 - wout[self.MSCRBProblem.Jc[a][0]] <= 0 for a in self.MSCRBProblem.LoadingCranes),
                     name="Cons8loadingfirstcont")

        m.addConstrs(
            (win[self.MSCRBProblem.Jc[a][i]] + self.MSCRBProblem.tq - win[self.MSCRBProblem.Jc[a][i + 1]] <= 0 for a in
             self.MSCRBProblem.UnloadingCranes for i in range(len(self.MSCRBProblem.Jc[a]) - 1)),
            name="Cons8UnloadingCrane")
        m.addConstrs((80 - win[self.MSCRBProblem.Jc[a][0]] <= 0 for a in self.MSCRBProblem.UnloadingCranes),
                     name="Cons8Unloadingfirstcont")

        m.addConstrs((win[i] + self.MSCRBProblem.tb <= wout[i] for b in self.MSCRBProblem.UnloadingCranes for a in
                      self.MSCRBProblem.LoadingCranes for i in self.MSCRBProblem.J + self.MSCRBProblem.Jvc[a] if
                      i not in self.MSCRBProblem.Jbc[b]), name="Cons9")

        m.addConstrs((win[i] == 0 for a in self.MSCRBProblem.cranes for i in self.MSCRBProblem.Jbc[a]), name="Cons11")

        m.addConstrs(
            (stack[self.MSCRBProblem.RJ[i][-1]] + self.MSCRBProblem.ts <= start[i] for i in self.MSCRBProblem.J if
             self.MSCRBProblem.RJ[i] != []), name="Cons14")

        m.addConstrs((self.MSCRBProblem.arj <= stack[i] for i in
                      self.MSCRBProblem.J + [self.MSCRBProblem.RJ[i][0] for i in self.MSCRBProblem.J if
                                             self.MSCRBProblem.RJ[i] != []]), name="Cons16")

        m.addConstrs((gp.quicksum(
            bin[self.MSCRBProblem.forbin[i][0], self.MSCRBProblem.forbin[i][1]] for i in
            range(len(self.MSCRBProblem.forbin))
            if self.MSCRBProblem.forbin[i][1] == j) -
                      gp.quicksum(bout[self.MSCRBProblem.forout[i][0], self.MSCRBProblem.forout[i][1]] for i in
                                  range(len(self.MSCRBProblem.forout)) if self.MSCRBProblem.forout[i][1] == j)
                      <= self.MSCRBProblem.bc - 1 for j in self.MSCRBProblem.Jcall + self.MSCRBProblem.JUall),
                     name="Cons17")

        m.addConstrs((win[self.MSCRBProblem.AllContBufintCranes[a][l]] - win[
            self.MSCRBProblem.AllContBufintCranes[a][i]] + 0.5 <= self.MSCRBProblem.M * bin[
                          self.MSCRBProblem.AllContBufintCranes[a][i], self.MSCRBProblem.AllContBufintCranes[a][l]]
                      for a in self.MSCRBProblem.cranes for i in
                      range(len(self.MSCRBProblem.AllContBufintCranes[a]) - 1)
                      for l in range(i + 1, len(self.MSCRBProblem.AllContBufintCranes[a]))), name="Cons18")

        m.addConstrs((win[self.MSCRBProblem.AllContBufintCranes[a][l]] - win[
            self.MSCRBProblem.AllContBufintCranes[a][i]] <= self.MSCRBProblem.M * bin[
                          self.MSCRBProblem.AllContBufintCranes[a][i], self.MSCRBProblem.AllContBufintCranes[a][l]]
                      for a in self.MSCRBProblem.cranes for i in range(1, len(self.MSCRBProblem.AllContBufintCranes[a]))
                      for l in range(i)), name="Cons19")

        m.addConstrs((win[j] - (wout[i] + self.MSCRBProblem.ts) >= self.MSCRBProblem.M * (bout[i, j] - 1) for a in
                      self.MSCRBProblem.cranes for j in self.MSCRBProblem.AllContBufintCranes[a] for i in
                      self.MSCRBProblem.AllContBufintCranes[a] if i != j), name="Cons20")

        m.setObjective(gp.quicksum(
            win[i] for crane in self.MSCRBProblem.UnloadingCranes for i in self.MSCRBProblem.Jc[crane]) + gp.quicksum(
            wout[j] for craneL in self.MSCRBProblem.LoadingCranes for j in self.MSCRBProblem.Jc[craneL]), GRB.MINIMIZE)

        m.setParam('OutputFlag', 0)
        time_limit = 180
        m.setParam("TimeLimit", time_limit)
        m.optimize()
        m._class_instance = self  # Store a reference to the class instance inside the model object

        run_time = m.getAttr('Runtime')
        obj_value = m.getAttr('ObjVal')
        status = "Opt." if m.status == 2 else "TimeL."
        gap = m.getAttr('MIPGap')

        self.gurobi_time = run_time
        self.objective_function = obj_value
        self.gurobi_status = status
        self.gurobi_gap = gap

    def calc_obj_kress_etal(self, beste_ever=None):

        objective = 0

        for crane in self.MSCRBProblem.cranes:
            crane.avl = 0

        for sc in self.MSCRBProblem.scs:
            sc.last_job_finish_time = 0
            sc.last_job = None
            sc.next_job = None

        for container in self.MSCRBProblem.containers:
            container.buffer_enter_time = None
            container.buffer_exit_time = None
            container.start_time = None
            container.end_time = None

        # define next job of each sc in the beginning
        for i, sc in enumerate(self.MSCRBProblem.scs):
            if not self.allocated_jobs[i]:
                sc.next_job = None
            else:
                sc.next_job = self.allocated_jobs[i][0]

        for straddleC_index, straddleC in enumerate(self.allocated_jobs):
            for order, container in enumerate(straddleC):
                # Assign the indices to the relevant container object
                container.assignment_index = (straddleC_index, order)

        # initialize J_bc for each crane; their buffer enter times are 0
        # and adding them in the buffer
        for crane in self.MSCRBProblem.cranes:
            for container in crane.Jbc:
                container.buffer_enter_time = 0
                # crane.buffer.add_container(container, 0)

        for crane in self.MSCRBProblem.cranes:
            if crane.kind == "L":
                for container in crane.list_of_containers:
                    if container.buffer_enter_time is not None:
                        container.buffer_exit_time = crane.avl
                        # crane.buffer.remove_container(container, crane.avl)
                        crane.avl += self.MSCRBProblem.tq
                        objective += container.buffer_exit_time
            else:

                spot = self.MSCRBProblem.bc - len(crane.Jbc)
                for container in crane.list_of_containers[len(crane.Jbc):len(crane.Jbc) + spot]:
                    container.buffer_enter_time = crane.avl + self.MSCRBProblem.tq
                    crane.avl += self.MSCRBProblem.tq
                    objective += container.buffer_enter_time

        # L loop.
        L = []
        while True:
            # Clear the previous set of containers
            L.clear()

            for crane in self.MSCRBProblem.cranes:
                if crane.kind == "L":
                    index, first_unset = next(((i, container) for i, container in enumerate(crane.list_of_containers) if
                                               container.buffer_enter_time is None and container.buffer_exit_time is None),
                                              (None, None))
                    if first_unset is None:
                        continue

                    valid_containers = [container for container in
                                        crane.list_of_containers[index: index + self.MSCRBProblem.bc] if
                                        container.buffer_enter_time is None]

                    L.extend(valid_containers)

                else:
                    valid_containers = [container for container in crane.list_of_containers if
                                        container.buffer_enter_time
                                        is not None and container.buffer_exit_time is None]

                    L.extend(valid_containers)

            # If no containers were added, L is empty, break the loop L
            if not L:
                break

            for container in L:
                if isinstance(container.container_above,
                              M.Container) and container.container_above.start_time is None:
                    index_Job = L.index(container)
                    L[index_Job] = container.container_above

            # no risk to fix variable 2
            status_of_any_sc = False
            for the_sc in self.MSCRBProblem.scs:
                if the_sc.next_job is None:
                    continue
                if the_sc.next_job in L:
                    container = the_sc.next_job
                    crane = container.crane
                    if container.kind == "R":
                        container.start_time = \
                            self.MSCRBProblem.Tunloaded[the_sc if not the_sc.last_job else the_sc.last_job][
                                container] + the_sc.last_job_finish_time
                        container.end_time = container.start_time + self.MSCRBProblem.tjob[container]
                        the_sc.last_job_finish_time = container.end_time
                        the_sc.last_job = container
                        the_sc.next_job_index = container.assignment_index[1] + 1
                        if container != self.allocated_jobs[container.assignment_index[0]][-1]:
                            the_sc.next_job = self.allocated_jobs[container.assignment_index[0]][the_sc.next_job_index]
                        else:
                            the_sc.next_job = None
                        status_of_any_sc = True

                    elif container.kind == "L":
                        if isinstance(container.container_above, M.Container):
                            if container.container_above.start_time is None:
                                continue
                            else:
                                restacking_time = (container.container_above.start_time +
                                                   self.MSCRBProblem.tv + self.MSCRBProblem.ts)
                                container.start_time = max(self.MSCRBProblem.Tunloaded
                                                           [the_sc if not the_sc.last_job else the_sc.last_job][
                                                               container] + the_sc.last_job_finish_time,
                                                           restacking_time)
                                container.end_time = container.start_time + self.MSCRBProblem.tjob[container]

                        else:
                            container.start_time = \
                                self.MSCRBProblem.Tunloaded[the_sc if not the_sc.last_job else the_sc.last_job][
                                    container] + the_sc.last_job_finish_time
                            container.end_time = container.start_time + self.MSCRBProblem.tjob[container]

                        buffer_available1 = 0

                        if container.order_index - len(crane.Jbc) >= self.MSCRBProblem.bc:
                            current_buffer_usage = 0
                            # Create a list of events where each event is a tuple of (time, change in buffer usage)
                            events = []
                            for bf_containers in crane.list_of_containers[
                                :container.order_index + self.MSCRBProblem.bc]:
                                if bf_containers.buffer_enter_time is not None:
                                    events.append((bf_containers.buffer_enter_time, 1))
                                if bf_containers.buffer_exit_time is not None:
                                    events.append((bf_containers.buffer_exit_time, -1))

                            # Sort events by time
                            events.sort(key=lambda x: x[0])

                            for event in events:
                                time, change = event
                                if change == 1:
                                    current_buffer_usage += 1
                                else:
                                    if current_buffer_usage == self.MSCRBProblem.bc:
                                        buffer_available1 = time + self.MSCRBProblem.ts
                                    current_buffer_usage -= 1

                        # buffer_available_at = crane.buffer.check_buffer_over_time()
                        container.buffer_enter_time = max(container.end_time, buffer_available1)
                        # crane.buffer.add_container(container, container.buffer_enter_time)

                        the_sc.last_job_finish_time = container.buffer_enter_time
                        the_sc.last_job = container
                        the_sc.next_job_index = container.assignment_index[1] + 1
                        if container != self.allocated_jobs[container.assignment_index[0]][-1]:
                            the_sc.next_job = self.allocated_jobs[container.assignment_index[0]][the_sc.next_job_index]
                        else:
                            the_sc.next_job = None
                        status_of_any_sc = True

                    else:
                        # unloading containers' variable 2 fixed here
                        container_ready = container.buffer_enter_time if container in crane.Jbc \
                            else container.buffer_enter_time + self.MSCRBProblem.tb
                        container.start_time = max(container_ready,
                                                   self.MSCRBProblem.Tunloaded[the_sc if not the_sc.last_job
                                                   else the_sc.last_job][container] + the_sc.last_job_finish_time)
                        container.end_time = container.start_time + self.MSCRBProblem.tjob[container]
                        the_sc.last_job_finish_time = container.end_time
                        the_sc.last_job = container
                        the_sc.next_job_index = container.assignment_index[1] + 1
                        if container != self.allocated_jobs[container.assignment_index[0]][-1]:
                            the_sc.next_job = self.allocated_jobs[container.assignment_index[0]][the_sc.next_job_index]
                        else:
                            the_sc.next_job = None
                        status_of_any_sc = True
                        container.buffer_exit_time = container.start_time
                        # crane.buffer.remove_container(container, container.buffer_exit_time)

            if not status_of_any_sc:
                return False

            # fix variables 1
            for crane in self.MSCRBProblem.cranes:
                if crane.kind == "L":
                    for container in crane.list_of_containers:
                        if container.buffer_enter_time is not None and container.buffer_exit_time is \
                                None and crane.list_of_containers[
                            container.order_index - 1].buffer_exit_time is not None:
                            container_ready = container.buffer_enter_time + self.MSCRBProblem.tb
                            process_time_for_loading_crane = max(container_ready, crane.avl)
                            container.buffer_exit_time = process_time_for_loading_crane
                            # crane.buffer.remove_container(container, container.buffer_exit_time)
                            crane.avl = process_time_for_loading_crane + self.MSCRBProblem.tq
                            objective += container.buffer_exit_time

                else:
                    for container in crane.list_of_containers:
                        if container.buffer_enter_time is None:
                            if container.order_index >= self.MSCRBProblem.bc:
                                current_buffer_usage = container.order_index + 1

                                due_date = crane.avl + self.MSCRBProblem.tq - self.MSCRBProblem.ts
                                for bef_container_un in crane.list_of_containers[:container.order_index]:
                                    if bef_container_un.buffer_exit_time is not None:
                                        if bef_container_un.buffer_exit_time <= due_date:
                                            current_buffer_usage -= 1

                                if current_buffer_usage <= self.MSCRBProblem.bc:
                                    container.buffer_enter_time = crane.avl + self.MSCRBProblem.tq
                                    crane.avl = container.buffer_enter_time
                                    objective += container.buffer_enter_time

                                else:
                                    containers_left_later = [container for container in
                                                             crane.list_of_containers[:container.order_index]
                                                             if container.buffer_exit_time is not None and
                                                             container.buffer_exit_time >= due_date]
                                    if not containers_left_later:
                                        break
                                    can_put = min(c.buffer_exit_time for c in containers_left_later)
                                    container.buffer_enter_time = can_put + self.MSCRBProblem.ts
                                    crane.avl = container.buffer_enter_time
                                    objective += container.buffer_enter_time

                            break

            if beste_ever is not None and objective >= beste_ever:
                return False
        return objective

    def greedy_kress_etal(self):

        self.allocated_jobs = [[] for _ in range(len(self.MSCRBProblem.scs))]

        p = self.MSCRBProblem
        objective = 0

        # Reset cranes
        for crane in p.cranes:
            crane.avl = 0

        # Reset SCs
        for sc in p.scs:
            sc.last_job_finish_time = 0
            sc.last_job = None
            sc.last_position = sc.start_position

        # Reset containers
        for c in p.containers:
            c.buffer_enter_time = None  # win
            c.buffer_exit_time = None  # wout
            c.start_time = None  # w (restack), also used as SC start time
            c.end_time = None
            c.sc_index = None

        # Set order_index for containers in each crane list
        for crane in p.cranes:
            for order_index, cont in enumerate(crane.list_of_containers):
                cont.order_index = order_index

        # Initialize: containers in buffer at start have win = 0
        for crane in p.cranes:
            for cont in crane.Jbc:
                cont.buffer_enter_time = 0

        crane_done = {crane: False for crane in p.cranes}

        while True:
            # 1) Let cranes work as much as possible and build candidate list L
            L = []

            for crane in p.cranes:
                if crane_done[crane]:
                    continue

                seq = crane.list_of_containers

                # -------------------------
                # Loading crane
                # -------------------------
                if crane.kind == "L":
                    while True:
                        # first i with wout unset
                        i = 0
                        while i < len(seq) and seq[i].buffer_exit_time is not None:
                            i += 1

                        if i >= len(seq):
                            crane_done[crane] = True
                            break

                        j = seq[i]

                        if j.buffer_enter_time is not None:
                            if i == 0:
                                j.buffer_exit_time = max(j.buffer_enter_time, 0)
                            else:
                                prev = seq[i - 1]
                                j.buffer_exit_time = max(prev.buffer_exit_time + p.tq, j.buffer_enter_time + p.tb)

                            objective += j.buffer_exit_time
                            # continue letting the crane work
                            continue

                        if i == 0:
                            due_date = 0
                        else:
                            prev = seq[i - 1]
                            due_date = prev.buffer_exit_time + p.tq - p.tb - p.tjob[j]

                        buf_avail_at = 0
                        if i >= p.bc:
                            events = []
                            for c2 in seq:
                                if c2.buffer_enter_time is not None:
                                    events.append((c2.buffer_enter_time, +1))  # in
                                if c2.buffer_exit_time is not None:
                                    events.append((c2.buffer_exit_time, -1))  # out

                            events.sort(key=lambda x: (x[0], x[1]))

                            buffer_status = 0
                            buf_avail_at = 0
                            for t, change in events:
                                if change == +1:
                                    buffer_status += 1
                                else:
                                    if buffer_status == p.bc:
                                        buf_avail_at = t + p.ts
                                    buffer_status -= 1

                        chain = []
                        r = j.container_above
                        while isinstance(r, M.Container) and r.kind == "R":
                            chain.append(r)
                            r = r.container_above
                        chain = list(reversed(chain))

                        first_unset = None
                        for rr in chain:
                            if rr.start_time is None:
                                first_unset = rr
                                break

                        if first_unset is not None:
                            L.append({
                                "job": first_unset,
                                "main": j,
                                "crane": crane,
                                "due": due_date - p.ts - p.tv,
                                "earliest": 0,
                                "job_type": "R"
                            })
                        else:

                            if len(chain) > 0:
                                closest = chain[-1]
                                buf_avail_at = max(buf_avail_at, closest.start_time + p.ts + p.tv + p.tjob[j])

                            L.append({
                                "job": j,
                                "main": j,
                                "crane": crane,
                                "due": due_date,
                                "earliest": buf_avail_at,  # lower bound on win
                                "job_type": "L"
                            })

                        break

                # -------------------------
                # Unloading crane
                # -------------------------
                else:  # crane.kind == "U"
                    while True:
                        i = 0
                        while i < len(seq) and seq[i].buffer_enter_time is not None:
                            i += 1

                        if i >= len(seq):
                            crane_done[crane] = True
                            break

                        due_date = 0 if i == 0 else seq[i - 1].buffer_enter_time + p.tq

                        buffer_status = i + 1
                        k = 0
                        while k < len(seq) and seq[k].buffer_exit_time is not None and seq[
                            k].buffer_exit_time <= due_date - p.ts:
                            buffer_status -= 1
                            k += 1

                        if buffer_status <= p.bc:
                            seq[i].buffer_enter_time = due_date
                            objective += seq[i].buffer_enter_time
                            continue  # try to unload the next one too

                        if k < len(seq) and seq[k].buffer_exit_time is not None:
                            seq[i].buffer_enter_time = seq[k].buffer_exit_time + p.ts
                            objective += seq[i].buffer_enter_time
                            continue

                        pickup = seq[k]
                        earliest = pickup.buffer_enter_time if pickup in pickup.crane.Jbc else pickup.buffer_enter_time + p.tb

                        chain = []
                        r = pickup.container_above
                        while isinstance(r, M.Container) and r.kind == "R":
                            chain.append(r)
                            r = r.container_above
                        chain = list(reversed(chain))

                        first_unset = None
                        for rr in chain:
                            if rr.start_time is None:
                                first_unset = rr
                                break

                        if first_unset is not None:
                            L.append({
                                "job": first_unset,
                                "main": pickup,
                                "crane": crane,
                                "due": due_date - p.ts,
                                "earliest": 0,
                                "job_type": "R"
                            })
                        else:

                            if len(chain) > 0:
                                closest = chain[-1]
                                loaded_travel = pickup.start_position.distance(pickup.end_position) * p.pv
                                earliest = max(earliest, closest.start_time + p.ts - p.tv - loaded_travel)

                            L.append({
                                "job": pickup,
                                "main": pickup,
                                "crane": crane,
                                "due": due_date,
                                "earliest": earliest,  # lower bound on wout
                                "job_type": "U"
                            })

                        break  # at most one candidate from this crane

            if len(L) == 0:
                break

            # 2) Pick job with smallest due date
            chosen = min(L, key=lambda x: x["due"])

            job = chosen["job"]
            job_type = chosen["job_type"]
            earliest = chosen["earliest"]

            # 3) Choose SC that arrives first at the job origin
            best_sc = None
            best_idx = -1
            best_arrival = 10 ** 18
            for idx, sc in enumerate(p.scs):
                if sc.last_job is None:
                    arrival = sc.last_job_finish_time + p.Tunloaded[sc][job]
                else:
                    arrival = sc.last_job_finish_time + p.Tunloaded[sc.last_job][job]
                if arrival < best_arrival:
                    best_arrival = arrival
                    best_sc = sc
                    best_idx = idx

            loaded_travel = job.start_position.distance(job.end_position) * p.pv
            tjob = 2 * p.tv + loaded_travel  # should equal p.tjob[job]

            if job.kind == "R":
                wj = max(earliest, best_arrival)
                job.start_time = wj
                job.end_time = wj + tjob
                best_sc.last_job = job
                best_sc.last_job_finish_time = job.end_time
                job.sc_index = best_idx
                self.allocated_jobs[best_idx].append(job)

            elif job.kind == "L":
                win = max(earliest, best_arrival + tjob)
                job.buffer_enter_time = win
                job.start_time = win - tjob
                job.end_time = win
                best_sc.last_job = job
                best_sc.last_job_finish_time = win
                job.sc_index = best_idx
                self.allocated_jobs[best_idx].append(job)

            else:  # job.kind == "U"
                wout = max(earliest, best_arrival)
                job.buffer_exit_time = wout
                job.start_time = wout
                job.end_time = wout + tjob
                best_sc.last_job = job
                best_sc.last_job_finish_time = job.end_time
                job.sc_index = best_idx
                self.allocated_jobs[best_idx].append(job)

        for crane in p.cranes:
            if crane.kind != "U":
                continue
            for cont in crane.list_of_containers:
                if cont.buffer_enter_time is not None and cont.buffer_exit_time is None:
                    # pick an arbitrary SC (first) and do it sequentially
                    sc = p.scs[0]
                    if sc.last_job is None:
                        arrival = sc.last_job_finish_time + p.Tunloaded[sc][cont]
                    else:
                        arrival = sc.last_job_finish_time + p.Tunloaded[sc.last_job][cont]
                    wout = max(cont.buffer_enter_time + p.tb, arrival)
                    loaded_travel = cont.start_position.distance(cont.end_position) * p.pv
                    tjob = 2 * p.tv + loaded_travel
                    cont.buffer_exit_time = wout
                    cont.start_time = wout
                    cont.end_time = wout + tjob
                    sc.last_job = cont
                    sc.last_job_finish_time = cont.end_time
                    cont.sc_index = 0
                    self.allocated_jobs[0].append(cont)

        self.objective_function = objective
        return objective

    def greedy_randomized(self, rnd=None, alpha=0.2, seed_try=1):

        self.allocated_jobs = [[] for _ in range(len(self.MSCRBProblem.scs))]

        if rnd is None:
            rnd = random.Random(seed_try)

        p = self.MSCRBProblem
        objective = 0

        # Reset cranes
        for crane in p.cranes:
            crane.avl = 0

        # Reset SCs
        for sc in p.scs:
            sc.last_job_finish_time = 0
            sc.last_job = None
            sc.last_position = sc.start_position

        # Reset containers
        for c in p.containers:
            c.buffer_enter_time = None  # win
            c.buffer_exit_time = None  # wout
            c.start_time = None  # w (restack), also used as SC start time
            c.end_time = None
            c.sc_index = None

        # Set order_index for containers in each crane list
        for crane in p.cranes:
            for order_index, cont in enumerate(crane.list_of_containers):
                cont.order_index = order_index

        # Initialize: containers in buffer at start have win = 0
        for crane in p.cranes:
            for cont in crane.Jbc:
                cont.buffer_enter_time = 0

        crane_done = {crane: False for crane in p.cranes}

        while True:
            # 1) Let cranes work as much as possible and build candidate list L
            L = []

            for crane in p.cranes:
                if crane_done[crane]:
                    continue

                seq = crane.list_of_containers

                # -------------------------
                # Loading crane
                # -------------------------
                if crane.kind == "L":
                    while True:
                        i = 0
                        while i < len(seq) and seq[i].buffer_exit_time is not None:
                            i += 1

                        if i >= len(seq):
                            crane_done[crane] = True
                            break

                        j = seq[i]

                        if j.buffer_enter_time is not None:
                            if i == 0:
                                j.buffer_exit_time = max(j.buffer_enter_time, 0)
                            else:
                                prev = seq[i - 1]
                                j.buffer_exit_time = max(prev.buffer_exit_time + p.tq, j.buffer_enter_time + p.tb)

                            objective += j.buffer_exit_time
                            continue

                        if i == 0:
                            due_date = 0
                        else:
                            prev = seq[i - 1]
                            due_date = prev.buffer_exit_time + p.tq - p.tb - p.tjob[j]

                        buf_avail_at = 0
                        if i >= p.bc:
                            events = []
                            for c2 in seq:
                                if c2.buffer_enter_time is not None:
                                    events.append((c2.buffer_enter_time, +1))  # in
                                if c2.buffer_exit_time is not None:
                                    events.append((c2.buffer_exit_time, -1))  # out

                            events.sort(key=lambda x: (x[0], x[1]))

                            buffer_status = 0
                            buf_avail_at = 0
                            for t, change in events:
                                if change == +1:
                                    buffer_status += 1
                                else:
                                    if buffer_status == p.bc:
                                        buf_avail_at = t + p.ts
                                    buffer_status -= 1

                        chain = []
                        r = j.container_above
                        while isinstance(r, M.Container) and r.kind == "R":
                            chain.append(r)
                            r = r.container_above
                        chain = list(reversed(chain))

                        first_unset = None
                        for rr in chain:
                            if rr.start_time is None:
                                first_unset = rr
                                break

                        if first_unset is not None:
                            L.append({
                                "job": first_unset,
                                "main": j,
                                "crane": crane,
                                "due": due_date - p.ts - p.tv,
                                "earliest": 0,
                                "job_type": "R"
                            })
                        else:

                            if len(chain) > 0:
                                closest = chain[-1]
                                buf_avail_at = max(buf_avail_at, closest.start_time + p.ts + p.tv + p.tjob[j])

                            L.append({
                                "job": j,
                                "main": j,
                                "crane": crane,
                                "due": due_date,
                                "earliest": buf_avail_at,  # lower bound on win
                                "job_type": "L"
                            })

                        break

                # -------------------------
                # Unloading crane
                # -------------------------
                else:  # crane.kind == "U"
                    while True:
                        i = 0
                        while i < len(seq) and seq[i].buffer_enter_time is not None:
                            i += 1

                        if i >= len(seq):
                            crane_done[crane] = True
                            break

                        due_date = 0 if i == 0 else seq[i - 1].buffer_enter_time + p.tq

                        buffer_status = i + 1
                        k = 0
                        while k < len(seq) and seq[k].buffer_exit_time is not None and seq[
                            k].buffer_exit_time <= due_date - p.ts:
                            buffer_status -= 1
                            k += 1

                        if buffer_status <= p.bc:
                            seq[i].buffer_enter_time = due_date
                            objective += seq[i].buffer_enter_time
                            continue  # try to unload the next one too

                        if k < len(seq) and seq[k].buffer_exit_time is not None:
                            seq[i].buffer_enter_time = seq[k].buffer_exit_time + p.ts
                            objective += seq[i].buffer_enter_time
                            continue

                        pickup = seq[k]
                        earliest = pickup.buffer_enter_time if pickup in pickup.crane.Jbc else pickup.buffer_enter_time + p.tb

                        chain = []
                        r = pickup.container_above
                        while isinstance(r, M.Container) and r.kind == "R":
                            chain.append(r)
                            r = r.container_above
                        chain = list(reversed(chain))

                        first_unset = None
                        for rr in chain:
                            if rr.start_time is None:
                                first_unset = rr
                                break

                        if first_unset is not None:
                            L.append({
                                "job": first_unset,
                                "main": pickup,
                                "crane": crane,
                                "due": due_date - p.ts,
                                "earliest": 0,
                                "job_type": "R"
                            })
                        else:
                            # If restacks exist and are done, adjust earliest as in C unloading formula:
                            # earliest >= wD + ts - tv - loaded_travel
                            if len(chain) > 0:
                                closest = chain[-1]
                                loaded_travel = pickup.start_position.distance(pickup.end_position) * p.pv
                                earliest = max(earliest, closest.start_time + p.ts - p.tv - loaded_travel)

                            L.append({
                                "job": pickup,
                                "main": pickup,
                                "crane": crane,
                                "due": due_date,
                                "earliest": earliest,  # lower bound on wout
                                "job_type": "U"
                            })

                        break  # at most one candidate from this crane

            if len(L) == 0:
                break

            # 2) Pick job with smallest due date
            chosen = min(L, key=lambda x: x["due"])

            job = chosen["job"]
            job_type = chosen["job_type"]
            earliest = chosen["earliest"]

            sc_scores = []
            for idx, sc in enumerate(p.scs):
                if sc.last_job is None:
                    arrival = sc.last_job_finish_time + p.Tunloaded[sc][job]
                else:
                    arrival = sc.last_job_finish_time + p.Tunloaded[sc.last_job][job]
                sc_scores.append((arrival, idx, sc))

            # sort best -> worst (smallest arrival first)
            sc_scores.sort(key=lambda t: t[0])

            # size of restricted candidate list
            if alpha <= 0:
                k = 1
            else:
                k = max(1, int(math.ceil(alpha * len(sc_scores))))

            _, best_idx, best_sc = rnd.choice(sc_scores[:k])
            best_arrival = sc_scores[0][0]
            best_arrival = next(a for (a, i, _) in sc_scores[:k] if i == best_idx)

            # 4) Fix time variables for the selected job with respect to earliest and SC arrival
            tjob = p.tjob[job]

            if job.kind == "R":
                wj = max(earliest, best_arrival)
                job.start_time = wj
                job.end_time = wj + tjob
                best_sc.last_job = job
                best_sc.last_job_finish_time = job.end_time
                job.sc_index = best_idx
                self.allocated_jobs[best_idx].append(job)

            elif job.kind == "L":
                win = max(earliest, best_arrival + tjob)
                job.buffer_enter_time = win
                job.start_time = win - tjob
                job.end_time = win
                best_sc.last_job = job
                best_sc.last_job_finish_time = win
                job.sc_index = best_idx
                self.allocated_jobs[best_idx].append(job)

            else:  # job.kind == "U"
                # unloading pickup: SC sets wout (start lifting from buffer)
                wout = max(earliest, best_arrival)
                job.buffer_exit_time = wout
                job.start_time = wout
                job.end_time = wout + tjob
                best_sc.last_job = job
                best_sc.last_job_finish_time = job.end_time
                job.sc_index = best_idx
                self.allocated_jobs[best_idx].append(job)

        for crane in p.cranes:
            if crane.kind != "U":
                continue
            for cont in crane.list_of_containers:
                if cont.buffer_enter_time is not None and cont.buffer_exit_time is None:
                    # pick an arbitrary SC (first) and do it sequentially
                    sc = p.scs[0]
                    if sc.last_job is None:
                        arrival = sc.last_job_finish_time + p.Tunloaded[sc][cont]
                    else:
                        arrival = sc.last_job_finish_time + p.Tunloaded[sc.last_job][cont]
                    wout = max(cont.buffer_enter_time + p.tb, arrival)
                    loaded_travel = cont.start_position.distance(cont.end_position) * p.pv
                    tjob = 2 * p.tv + loaded_travel
                    cont.buffer_exit_time = wout
                    cont.start_time = wout
                    cont.end_time = wout + tjob
                    sc.last_job = cont
                    sc.last_job_finish_time = cont.end_time
                    cont.sc_index = 0
                    self.allocated_jobs[0].append(cont)

        self.objective_function = objective
        return objective

    # ========================================= Local Search ===============================================================

    def local_search_with_time(self, time_limit=180, start_time_grasp_run=None):
        if start_time_grasp_run is None:
            start_time_grasp_run = time.time()
        number_of_SCs = self.MSCRBProblem.nv
        has_improvement = False

        for i in range(0, number_of_SCs):
            for j in range(0, number_of_SCs):
                if i != j:
                    current_time = time.time() - start_time_grasp_run
                    if current_time > time_limit:
                        return has_improvement
                    was_improvement = self.LS_2exchange_best_found(i, j)
                    if was_improvement:
                        has_improvement = True

        for i in range(0, number_of_SCs):
            for j in range(0, number_of_SCs):
                if i != j:
                    current_time = time.time() - start_time_grasp_run
                    if current_time > time_limit:
                        return has_improvement
                    was_improvement = self.LS_2relocate_best_found(i, j)
                    if was_improvement:
                        has_improvement = True

        for i in range(0, number_of_SCs):
            current_time = time.time() - start_time_grasp_run
            if current_time > time_limit:
                return has_improvement
            was_improvement = self.LS_2opt_best_found(i)
            if was_improvement:
                has_improvement = True

        for i in range(0, number_of_SCs):
            for j in range(0, number_of_SCs):
                if i != j:
                    current_time = time.time() - start_time_grasp_run
                    if current_time > time_limit:
                        return has_improvement
                    was_improvement = self.LS_2opt_2route_best_found(i, j)
                    if was_improvement:
                        has_improvement = True

        return has_improvement

    def LS_2exchange_best_found(self, sc_index1, sc_index2):
        has_improvement = False
        current_objective_function = self.objective_function
        number_of_jobs1 = len(self.allocated_jobs[sc_index1])
        number_of_jobs2 = len(self.allocated_jobs[sc_index2])
        best_solution = MSCRBSolution(self.MSCRBProblem, name="Best_one")
        best_solution.allocated_jobs = self.copy_allocated_jobs()
        # best_solution.allocated_jobs = copy.copy(self.allocated_jobs)
        best_solution.objective_function = current_objective_function
        best_objective_function = current_objective_function

        for index1 in range(number_of_jobs1):
            for index2 in range(number_of_jobs2):
                # Try swapping jobs index1 and index2
                new_solution = MSCRBSolution(self.MSCRBProblem, name="New_one")
                new_solution.allocated_jobs = self.copy_allocated_jobs()
                new_solution.allocated_jobs[sc_index1][index1], new_solution.allocated_jobs[sc_index2][index2] = \
                    new_solution.allocated_jobs[sc_index2][index2], new_solution.allocated_jobs[sc_index1][index1]

                # Check if the new solution violates the constraint about restacking containers
                if any(container.kind == "R" for container in new_solution.allocated_jobs[sc_index1][3:]) or any(
                        container.kind == "R" for container in new_solution.allocated_jobs[sc_index2][3:]):
                    continue

                if any(container.order_index <= 3 for container in
                       new_solution.allocated_jobs[sc_index1][3:]) or any(
                    container.order_index <= 3 for container in new_solution.allocated_jobs[sc_index2][3:]):
                    continue
                # Calculate the objective function of the new solution
                new_objective_function = new_solution.calc_obj_kress_etal(best_objective_function)

                # If the new solution is better (than best), update the best solution
                if new_objective_function:
                    best_solution.allocated_jobs = new_solution.copy_allocated_jobs()
                    # best_solution.allocated_jobs = copy.copy(new_solution.allocated_jobs)
                    best_solution.objective_function = new_objective_function
                    best_objective_function = new_objective_function
                    has_improvement = True

        # If there's an improvement, update the allocated jobs and return True
        if has_improvement:
            self.allocated_jobs = best_solution.copy_allocated_jobs()
            # self.allocated_jobs = copy.copy(best_solution.allocated_jobs)
            self.objective_function = best_objective_function
            return True

        # If no improvement was found, return False
        return False

    def LS_2relocate_best_found(self, sc_index1, sc_index2):
        has_improvement = False
        current_objective_function = self.objective_function
        number_of_jobs1 = len(self.allocated_jobs[sc_index1])
        if number_of_jobs1 == 1:
            return False
        number_of_jobs2 = len(self.allocated_jobs[sc_index2])
        best_solution = MSCRBSolution(self.MSCRBProblem, name="Best_one")
        best_solution.allocated_jobs = self.copy_allocated_jobs()
        best_solution.objective_function = current_objective_function
        best_objective_function = current_objective_function

        for index1 in range(number_of_jobs1):
            for index2 in range(number_of_jobs2):
                # Try relocating job index1 from sc_index1 to sc_index2
                new_solution = MSCRBSolution(self.MSCRBProblem, name="New_one")
                new_solution.allocated_jobs = self.copy_allocated_jobs()
                container_to_relocate = new_solution.allocated_jobs[sc_index1][index1]
                new_solution.allocated_jobs[sc_index1].remove(container_to_relocate)
                new_solution.allocated_jobs[sc_index2].insert(index2, container_to_relocate)

                # Check if the new solution violates the constraint about the "R" kind containers
                if container_to_relocate.kind == "R" and (index2 > 1 or
                                                          any(container.kind == "R" for container in
                                                              new_solution.allocated_jobs[sc_index2][2:])):
                    continue

                # Calculate the objective function of the new solution
                new_objective_function = new_solution.calc_obj_kress_etal(best_objective_function)

                if new_objective_function:
                    best_solution.allocated_jobs = new_solution.copy_allocated_jobs()
                    best_solution.objective_function = new_objective_function
                    best_objective_function = new_objective_function
                    has_improvement = True

        # If there's an improvement, update the allocated jobs and return True
        if has_improvement:
            self.allocated_jobs = best_solution.copy_allocated_jobs()
            self.objective_function = best_objective_function
            return True

        # If no improvement was found, return False
        return False

    def LS_2opt_best_found(self, sc_index1):
        has_improvement = False
        current_objective_function = self.objective_function
        number_of_jobs1 = len(self.allocated_jobs[sc_index1])
        best_solution = MSCRBSolution(self.MSCRBProblem, name="Best_one")
        best_solution.allocated_jobs = self.copy_allocated_jobs()
        best_solution.objective_function = current_objective_function
        best_objective_function = current_objective_function

        for index1 in range(0, number_of_jobs1 - 1):
            for index2 in range(index1 + 2, number_of_jobs1):
                # Create a new solution by reversing a section of route1
                new_solution = MSCRBSolution(self.MSCRBProblem, name="New_one")
                new_solution.allocated_jobs = self.copy_allocated_jobs()
                new_solution.allocated_jobs[sc_index1] = (new_solution.allocated_jobs[sc_index1][:index1] +
                                                          new_solution.allocated_jobs[sc_index1][index1:index2][
                                                              ::-1] +
                                                          new_solution.allocated_jobs[sc_index1][index2:])

                # Checking if the new solution violates the "R" kind container constraint
                if any(container.kind == "R" for container in new_solution.allocated_jobs[sc_index1][2:]):
                    continue

                new_objective_function = new_solution.calc_obj_kress_etal(best_objective_function)

                if new_objective_function:
                    best_solution.allocated_jobs = new_solution.copy_allocated_jobs()
                    best_solution.objective_function = new_objective_function
                    best_objective_function = new_objective_function
                    has_improvement = True

        if has_improvement:
            self.allocated_jobs = best_solution.copy_allocated_jobs()
            self.objective_function = best_objective_function
            return True

        # If no improvement was found, return False
        return False

    def LS_2opt_2route_best_found(self, sc_index1, sc_index2):
        has_improvement = False
        current_objective_function = self.objective_function
        number_of_jobs1 = len(self.allocated_jobs[sc_index1])
        number_of_jobs2 = len(self.allocated_jobs[sc_index2])
        best_solution = MSCRBSolution(self.MSCRBProblem, name="Best_one")
        best_solution.allocated_jobs = self.copy_allocated_jobs()
        best_solution.objective_function = current_objective_function
        best_objective_function = current_objective_function

        for index1 in range(0, number_of_jobs1):
            for index2 in range(0, number_of_jobs2):
                # Create a new solution by swapping edges between two routes
                new_solution = MSCRBSolution(self.MSCRBProblem, name="New_one")
                new_solution.allocated_jobs = self.copy_allocated_jobs()

                # Swap jobs index1 of sc_index1 with index2 of sc_index2
                temp = new_solution.allocated_jobs[sc_index1][index1:]
                new_solution.allocated_jobs[sc_index1][index1:] = new_solution.allocated_jobs[sc_index2][index2:]
                new_solution.allocated_jobs[sc_index2][index2:] = temp

                if any(container.kind == "R" for container in
                       new_solution.allocated_jobs[sc_index1][2:] + new_solution.allocated_jobs[sc_index2][3:]):
                    continue

                if any(container.order_index <= 3 for container in
                       new_solution.allocated_jobs[sc_index1][3:]) or any(
                    container.order_index <= 3 for container in new_solution.allocated_jobs[sc_index2][3:]):
                    continue

                new_objective_function = new_solution.calc_obj_kress_etal(best_objective_function)

                # If the new solution is better, update the best solution
                if new_objective_function:
                    best_solution.allocated_jobs = new_solution.copy_allocated_jobs()
                    best_solution.objective_function = new_objective_function
                    best_objective_function = new_objective_function
                    has_improvement = True

        # If there's an improvement, update the allocated jobs and return True
        if has_improvement:
            self.allocated_jobs = best_solution.copy_allocated_jobs()
            self.objective_function = best_objective_function
            return True

        # If no improvement was found, return False
        return False

    def local_search_for_VND_with_time(self, k, time_limit=3600, start_time_vns_run=None):
        if start_time_vns_run is None:
            start_time_vns_run = time.time()
        numOfSC = self.MSCRBProblem.nv
        has_improvement = False

        if k == 2:
            for i in range(0, numOfSC):
                for j in range(0, numOfSC):
                    if i != j:
                        current_time = time.time() - start_time_vns_run
                        if current_time > time_limit:
                            return has_improvement
                        was_improvement = self.LS_2exchange_best_found(i, j)
                        if was_improvement:
                            has_improvement = True
        elif k == 3:
            for i in range(0, numOfSC):
                for j in range(0, numOfSC):
                    if i != j:
                        current_time = time.time() - start_time_vns_run
                        if current_time > time_limit:
                            return has_improvement
                        was_improvement = self.LS_2relocate_best_found(i, j)
                        if was_improvement:
                            has_improvement = True
        elif k == 4:
            for i in range(0, numOfSC):
                for j in range(0, numOfSC):
                    if i != j:
                        current_time = time.time() - start_time_vns_run
                        if current_time > time_limit:
                            return has_improvement
                        was_improvement = self.LS_2opt_2route_best_found(i, j)
                        if was_improvement:
                            has_improvement = True

        else:
            for i in range(0, numOfSC):
                current_time = time.time() - start_time_vns_run
                if current_time > time_limit:
                    return has_improvement
                was_improvement = self.LS_2opt_best_found(i)
                if was_improvement:
                    has_improvement = True

        return has_improvement

    def local_search_for_CVND_with_time(self, k, time_limit=180, start_time_vns_run=None):
        if start_time_vns_run is None:
            start_time_vns_run = time.time()
        numOfSC = self.MSCRBProblem.nv
        has_improvement = False

        if k == 1:
            for i in range(0, numOfSC):
                for j in range(0, numOfSC):
                    if i != j:
                        current_time = time.time() - start_time_vns_run
                        if current_time > time_limit:
                            return has_improvement
                        was_improvement = self.LS_2exchange_best_found(i, j)
                        if was_improvement:
                            has_improvement = True
        elif k == 2:
            for i in range(0, numOfSC):
                for j in range(0, numOfSC):
                    if i != j:
                        current_time = time.time() - start_time_vns_run
                        if current_time > time_limit:
                            return has_improvement
                        was_improvement = self.LS_2relocate_best_found(i, j)
                        if was_improvement:
                            has_improvement = True
        elif k == 4:
            for i in range(0, numOfSC):
                for j in range(0, numOfSC):
                    if i != j:
                        current_time = time.time() - start_time_vns_run
                        if current_time > time_limit:
                            return has_improvement
                        was_improvement = self.LS_2opt_2route_best_found(i, j)
                        if was_improvement:
                            has_improvement = True

        else:
            for i in range(0, numOfSC):
                current_time = time.time() - start_time_vns_run
                if current_time > time_limit:
                    return has_improvement
                was_improvement = self.LS_2opt_best_found(i)
                if was_improvement:
                    has_improvement = True

        return has_improvement

    def shake_functions(self, m, rnd=None):

        if m == 1:
            is_shaken = self.shake_random_2_relocation(rnd)
        elif m == 2:
            is_shaken = self.shake_random_2_exchange(rnd)
        else:
            is_shaken = self.shake_random_3_relocation(rnd)

        return is_shaken

    def shake_random_3_relocation(self, rnd):
        number_of_SCs = self.MSCRBProblem.nv
        if number_of_SCs < 3:
            return False  # Cannot perform 3-opt

        sc_index1, sc_index2, sc_index3 = rnd.sample(range(number_of_SCs), 3)

        number_of_jobs1 = len(self.allocated_jobs[sc_index1])
        number_of_jobs2 = len(self.allocated_jobs[sc_index2])
        number_of_jobs3 = len(self.allocated_jobs[sc_index3])

        if number_of_jobs1 == 0 or number_of_jobs2 == 0 or number_of_jobs3 == 0:
            return False  # Cannot perform 3-opt with empty SCs

        # Randomly select one job from each SC
        job_index1 = rnd.randint(0, number_of_jobs1 - 1)
        job_index2 = rnd.randint(0, number_of_jobs2 - 1)
        job_index3 = rnd.randint(0, number_of_jobs3 - 1)

        # Remove the jobs from their original positions
        temp1 = self.allocated_jobs[sc_index1].pop(job_index1)
        temp2 = self.allocated_jobs[sc_index2].pop(job_index2)
        temp3 = self.allocated_jobs[sc_index3].pop(job_index3)

        # Place the removed jobs into new positions
        self.allocated_jobs[sc_index1].insert(job_index1, temp2)
        self.allocated_jobs[sc_index2].insert(job_index2, temp3)
        self.allocated_jobs[sc_index3].insert(job_index3, temp1)

        self.objective_function = self.calc_obj_kress_etal()
        if self.objective_function == False:
            return False
        return True

    def shake_random_2_relocation(self, rnd):
        number_of_SCs = self.MSCRBProblem.nv
        if number_of_SCs < 2:  # At least two SCs are needed for a relocation move
            return False

        # Randomly select a source SC
        sc_index_source = rnd.randint(0, number_of_SCs - 1)

        # the number of jobs for the source SC
        number_of_jobs_source = len(self.allocated_jobs[sc_index_source])

        if number_of_jobs_source <= 1:
            return False  # Cannot perform relocation, an empty source SC

        # randomly select a job from the source SC
        job_index_source = rnd.randint(0, number_of_jobs_source - 1)

        # Remove the selected job from the source SC and save it!
        temp_job = self.allocated_jobs[sc_index_source].pop(job_index_source)

        sc_index_dest = rnd.choice([i for i in range(number_of_SCs) if i != sc_index_source])

        number_of_jobs_dest = len(self.allocated_jobs[sc_index_dest])

        job_index_dest = rnd.randint(0, number_of_jobs_dest)

        # relocate the job at the selected position in the destination SC
        self.allocated_jobs[sc_index_dest].insert(job_index_dest, temp_job)

        self.objective_function = self.calc_obj_kress_etal()
        if self.objective_function == False:
            return False
        return True

    def shake_random_2_exchange(self, rnd):
        number_of_SCs = self.MSCRBProblem.nv
        if number_of_SCs < 2:  # At least two SCs are needed for a 2-exchange move
            return False

        # Randomly select the first SC
        sc_index_1 = rnd.randint(0, number_of_SCs - 1)
        number_of_jobs_1 = len(self.allocated_jobs[sc_index_1])

        # check the number of job of SC1
        if number_of_jobs_1 == 0:
            return False

        # select a container
        job_index_1 = rnd.randint(0, number_of_jobs_1 - 1)

        # second sc
        sc_index_2 = rnd.choice([i for i in range(number_of_SCs) if i != sc_index_1])
        number_of_jobs_2 = len(self.allocated_jobs[sc_index_2])

        # check the job number of the second sc
        if number_of_jobs_2 == 0:
            return False

        # select a container from the second sc
        job_index_2 = rnd.randint(0, number_of_jobs_2 - 1)

        # exchange them
        self.allocated_jobs[sc_index_1][job_index_1], self.allocated_jobs[sc_index_2][job_index_2] = \
            self.allocated_jobs[sc_index_2][job_index_2], self.allocated_jobs[sc_index_1][job_index_1]

        self.objective_function = self.calc_obj_kress_etal()
        if self.objective_function == False:
            return False
        return True


class CVND:
    def __init__(self, instance):
        self.vnd_instance = M.MSCRBProblem([], [], [])
        self.vnd_instance.read_from_file(instance)
        self.solution = MSCRBSolution(self.vnd_instance)

    def run(self, initial_solution=None, kmax=4, time_limit=180, start_time=None):
        start_vnd_time = time.time()

        if initial_solution is not None:
            self.solution = initial_solution
            greedy_value = None
        else:
            greedy_value = self.solution.greedy_kress_etal()
            self.solution.objective_function = greedy_value

        # greedy_value = self.solution.the_greedy()
        best_solution = MSCRBSolution(self.vnd_instance, name="Best VND")
        best_solution.allocated_jobs = self.solution.copy_allocated_jobs()
        best_solution.objective_function = self.solution.objective_function

        while True:  # Starting the cyclic loop
            improvement_in_cycle = False  # Flag to track any improvement in the full cycle

            for k in range(1, kmax + 1):
                if start_time is not None:
                    self.solution.local_search_for_CVND_with_time(k, time_limit=time_limit,
                                                                  start_time_vns_run=start_time)
                else:
                    self.solution.local_search_for_CVND_with_time(k, time_limit=time_limit,
                                                                  start_time_vns_run=start_vnd_time)
                improved_in_this_neighborhood, best_solution.allocated_jobs, best_solution.objective_function \
                    = self.neighborhood_change(best_solution)

                if improved_in_this_neighborhood:
                    improvement_in_cycle = True  # Mark that we found an improvement in this cycle

                # print(k, improvement_in_cycle)
            if not improvement_in_cycle:  # If no improvements in the full cycle, break out
                break

        end_vnd_time = time.time() - start_vnd_time

        self.solution.allocated_jobs = best_solution.copy_allocated_jobs()
        self.solution.objective_function = best_solution.objective_function
        vnd_result = best_solution.objective_function

        return greedy_value, vnd_result, end_vnd_time

    def neighborhood_change(self, best_sol):
        new_objective = self.solution.objective_function
        best_objective = best_sol.objective_function

        if new_objective < best_objective:
            best_sol.allocated_jobs = self.solution.copy_allocated_jobs()
            best_sol.objective_function = new_objective
            return True, best_sol.allocated_jobs, best_sol.objective_function  # Improvement found
        else:
            return False, best_sol.allocated_jobs, best_sol.objective_function  # No improvement


class VND:
    def __init__(self, instance):
        self.vnd_instance = M.MSCRBProblem()
        self.vnd_instance.read_from_file(instance)
        self.solution = MSCRBSolution(self.vnd_instance)

    def run(self, kmax=4, time_limit=180):
        start_vnd_time = time.time()
        greedy_value = self.solution.greedy_kress_etal()
        self.solution.objective_function = greedy_value
        best_solution = MSCRBSolution(self.vnd_instance, name="Best VND")
        best_solution.allocated_jobs = self.solution.copy_allocated_jobs()
        best_solution.objective_function = greedy_value

        k = 1
        while k <= kmax:
            self.solution.local_search_for_VND_with_time(k, time_limit=time_limit, start_time_vns_run=start_vnd_time)
            best_solution.allocated_jobs, best_solution.objective_function, k \
                = self.neighborhood_change(best_solution, k)
        end_vnd_time = time.time() - start_vnd_time

        self.solution.allocated_jobs = best_solution.copy_allocated_jobs()
        self.solution.objective_function = best_solution.objective_function
        vnd_result = best_solution.objective_function

        return greedy_value, vnd_result, end_vnd_time

    def neighborhood_change(self, best_sol, k):
        new_objective = self.solution.objective_function
        best_objective = best_sol.objective_function
        if new_objective < best_objective:
            best_sol.allocated_jobs = self.solution.copy_allocated_jobs()
            best_sol.objective_function = new_objective
            k = 1
        else:
            k += 1
        return best_sol.allocated_jobs, best_sol.objective_function, k


class B_VNS:
    def __init__(self, instance):
        self.vnd_instance = M.MSCRBProblem()
        self.vnd_instance.read_from_file(instance)
        self.solution = MSCRBSolution(self.vnd_instance)

    def run(self, m_max=3, time_limit=180, number_of_iterations=10000, seed_try=1):
        rnd = random.Random(seed_try)
        vns_start_time = time.time()
        greedy_value = self.solution.greedy_kress_etal()
        self.solution.objective_function = greedy_value
        self.solution.local_search_with_time(time_limit=time_limit, start_time_grasp_run=vns_start_time)
        vnd_time = time.time() - vns_start_time
        vnd_obj_val = self.solution.objective_function
        best_solution = MSCRBSolution(self.vnd_instance, name="Best VNS")
        best_solution.allocated_jobs = self.solution.copy_allocated_jobs()
        best_solution.objective_function = vnd_obj_val
        best_ever_vns = best_solution.objective_function

        best_solution_found_time = vnd_time
        i = 0
        time_limit_reached = False
        while i < number_of_iterations:
            m = 1
            while m <= m_max:
                new_solution = MSCRBSolution(self.vnd_instance, name="New VNS")
                new_solution.allocated_jobs = self.solution.copy_allocated_jobs()
                new_solution.objective_function = self.solution.objective_function

                if new_solution.shake_functions(m, rnd) == False:
                    self.solution.allocated_jobs = new_solution.copy_allocated_jobs()
                    self.solution.objective_function = sys.maxsize
                else:
                    self.solution.allocated_jobs = new_solution.copy_allocated_jobs()
                    self.solution.objective_function = new_solution.objective_function

                self.solution.local_search_with_time(time_limit=time_limit, start_time_grasp_run=vns_start_time)

                new_obj = self.solution.objective_function
                current_time = time.time() - vns_start_time

                if new_obj < best_ever_vns:
                    best_solution.allocated_jobs = self.solution.copy_allocated_jobs()
                    best_solution.objective_function = self.solution.objective_function
                    best_ever_vns = new_obj

                    best_solution_found_time = current_time

                    m = 1
                else:
                    m += 1
                if current_time > time_limit:
                    time_limit_reached = True
                    break
            i += 1
            if time_limit_reached:
                break

        vns_total_time = time.time() - vns_start_time
        return best_solution, greedy_value, vnd_obj_val, vnd_time, best_solution_found_time, vns_total_time, best_ever_vns


class Grasp:
    def __init__(self, instance):
        self.grasp_instance = M.MSCRBProblem()
        self.grasp_instance.read_from_file(instance)
        self.solution = MSCRBSolution(self.grasp_instance)

        self.alpha_start = 0
        self.alpha_end = 1
        self.number_of_alphas = 11
        self.alphas = [alpha for alpha in np.linspace(self.alpha_start, self.alpha_end, num=self.number_of_alphas)]

    def run(self, time_limit=180, seed_try=1):
        rnd = random.Random(seed_try)
        grasp_start_time = time.time()
        greedy_value = self.solution.greedy_kress_etal()
        self.solution.objective_function = greedy_value

        self.solution.local_search_with_time(time_limit=time_limit, start_time_grasp_run=grasp_start_time)
        ls_time = time.time() - grasp_start_time
        obj_value_after_ls = self.solution.objective_function
        best_solution = MSCRBSolution(self.grasp_instance, name="Best Grasp")
        best_solution.allocated_jobs = self.solution.copy_allocated_jobs()
        best_solution.objective_function = obj_value_after_ls
        best_ever = best_solution.objective_function
        best_solution_found_time = ls_time

        for i in range(1, 10000):

            alpha = rnd.choice(self.alphas)

            greedy_randomized_value = self.solution.greedy_randomized(rnd=rnd, alpha=alpha)

            self.solution.objective_function = greedy_randomized_value
            self.solution.local_search_with_time(time_limit=time_limit, start_time_grasp_run=grasp_start_time)
            value_to_comp = self.solution.objective_function
            current_time = time.time() - grasp_start_time

            if value_to_comp < best_ever:
                best_ever = value_to_comp
                best_solution.allocated_jobs = self.solution.copy_allocated_jobs()
                best_solution.objective_function = best_ever

                best_solution_found_time = current_time

            if current_time > time_limit:
                break

        grasp_total_time = time.time() - grasp_start_time

        return (best_solution, greedy_value, obj_value_after_ls, ls_time, best_solution_found_time,
                grasp_total_time, best_ever)


class k_opt_kress_etal:

    def __init__(self, mscrb_solution):
        self.sol = mscrb_solution
        self.p = mscrb_solution.MSCRBProblem
        self.scs = self.p.scs

        self.scratch = type(mscrb_solution)(self.p, name="3opt_kress_etal_scratch")

    def build_U_from_allocated_jobs(self, allocated_jobs):
        U = []
        sc_pos = []
        for sc_index, sc in enumerate(self.scs):
            sc_pos.append(len(U))
            U.append(sc)
            for job in allocated_jobs[sc_index]:
                U.append(job)
        return U, sc_pos

    def build_is_sc_pos(self, n, sc_pos):
        is_sc = [False] * n
        for pos in sc_pos:
            is_sc[pos] = True
        return is_sc

    def build_initial_succ_pos(self, n):
        return [(i + 1) % n for i in range(n)]

    def is_single_cycle_fast(self, succ_pos, visit_stamp, stamp):
        n = len(succ_pos)
        node = 0
        for _ in range(n):
            if visit_stamp[node] == stamp:
                return False
            visit_stamp[node] = stamp
            node = succ_pos[node]
        return node == 0

    def fill_allocated_jobs_from_succ_pos(self, U, sc_pos, is_sc_pos, succ_pos, scratch_alloc):
        n = len(U)
        max_steps = n + 1

        for k, spos in enumerate(sc_pos):
            route = scratch_alloc[k]
            route.clear()

            node_pos = succ_pos[spos]
            steps = 0
            while steps < max_steps and (not is_sc_pos[node_pos]):
                route.append(U[node_pos])
                node_pos = succ_pos[node_pos]
                steps += 1

        return scratch_alloc

    def run(self, iterations=1000, try_probab=0.9, seed_try=1, threshold=None, time_limit=180):
        if threshold is None:
            threshold = self.p.ts

        rnd = random.Random(seed_try)
        k_opt_start_time = time.time()
        best_alloc = self.sol.copy_allocated_jobs()

        U, sc_pos = self.build_U_from_allocated_jobs(best_alloc)
        n = len(U)
        if n == 0:
            self.sol.allocated_jobs = best_alloc
            self.sol.objective_function = 0.0
            return 0.0

        is_sc_pos = self.build_is_sc_pos(n, sc_pos)
        succ_pos = self.build_initial_succ_pos(n)

        scratch_alloc = [[] for _ in self.scs]

        self.scratch.allocated_jobs = best_alloc
        best_obj = self.scratch.calc_obj_kress_etal()
        if best_obj is False:
            return False

        visit_stamp = [0] * n
        stamp = 0

        iteration_count = 0

        # time setup
        t0 = time.perf_counter()
        deadline = None if (time_limit is None or time_limit <= 0) else (t0 + float(time_limit))

        def time_up():
            return deadline is not None and time.perf_counter() >= deadline

        is_single_cycle_fast = self.is_single_cycle_fast
        fill_alloc = self.fill_allocated_jobs_from_succ_pos
        scratch = self.scratch
        kress_eval = scratch.calc_obj_kress_etal

        while True:
            if iterations > 0 and iteration_count >= iterations:
                break

            iteration_count += 1

            accepted = False
            last_improvement = 0.0

            for i1 in range(n):
                v1_pos = succ_pos[i1]

                for i2 in range(i1 + 1, n):
                    v2_pos = succ_pos[i2]

                    for i3 in range(i2 + 1, n):
                        if rnd.random() > try_probab:
                            continue
                        if time_up():
                            break

                        v3_pos = succ_pos[i3]

                        best_case = 0
                        best_case_obj = best_obj
                        best_case_alloc = None

                        orig_i1, orig_i2, orig_i3 = v1_pos, v2_pos, v3_pos

                        # ----- case 1 -----
                        succ_pos[i1] = v2_pos
                        succ_pos[i2] = v3_pos
                        succ_pos[i3] = v1_pos

                        stamp += 1
                        if is_single_cycle_fast(succ_pos, visit_stamp, stamp):
                            temp_alloc = fill_alloc(U, sc_pos, is_sc_pos, succ_pos, scratch_alloc)
                            scratch.allocated_jobs = temp_alloc
                            temp_obj = kress_eval(beste_ever=best_obj)

                            if temp_obj is not False and temp_obj < best_case_obj:
                                best_case = 1
                                best_case_obj = temp_obj
                                best_case_alloc = [list(r) for r in temp_alloc]

                        # revert
                        succ_pos[i1], succ_pos[i2], succ_pos[i3] = orig_i1, orig_i2, orig_i3

                        # ----- case 2 -----
                        succ_pos[i1] = v3_pos
                        succ_pos[i3] = v2_pos
                        succ_pos[i2] = v1_pos

                        stamp += 1
                        if is_single_cycle_fast(succ_pos, visit_stamp, stamp):
                            temp_alloc = fill_alloc(U, sc_pos, is_sc_pos, succ_pos, scratch_alloc)
                            scratch.allocated_jobs = temp_alloc
                            temp_obj = kress_eval(beste_ever=best_obj)

                            if temp_obj is not False and temp_obj < best_case_obj:
                                best_case = 2
                                best_case_obj = temp_obj
                                best_case_alloc = [list(r) for r in temp_alloc]

                        # revert
                        succ_pos[i1], succ_pos[i2], succ_pos[i3] = orig_i1, orig_i2, orig_i3

                        if best_case != 0:
                            last_improvement = best_obj - best_case_obj
                            if last_improvement >= threshold:
                                best_obj = best_case_obj
                                best_alloc = best_case_alloc

                                if best_case == 1:
                                    succ_pos[i1] = v2_pos
                                    succ_pos[i2] = v3_pos
                                    succ_pos[i3] = v1_pos
                                else:  # best_case == 2
                                    succ_pos[i1] = v3_pos
                                    succ_pos[i3] = v2_pos
                                    succ_pos[i2] = v1_pos

                                accepted = True
                                break

                    if accepted:
                        break
                if accepted:
                    break

            if not accepted:
                break

            # if last_improvement < threshold:
            #     continue_search = False
        k_opt_end_time = time.time() - k_opt_start_time
        self.sol.allocated_jobs = best_alloc
        self.sol.objective_function = best_obj
        return best_obj, k_opt_end_time


# ========================================= CLI parsing ===============================================================

def parse_args():
    """
    Expected usage on the cluster (one method per job):

        python Algorithms_Main.py METHOD INSTANCE_FILE SEED

    Examples:
        python Algorithms_Main.py grasp instances_comp_gurobi/12345SEED_3QC_9SC_4BC_0.05R_14J.txt 1
        python Algorithms_Main.py vns   instances_comp_gurobi/12345SEED_3QC_9SC_4BC_0.05R_14J.txt 5
        python Algorithms_Main.py vnd   instances_comp_gurobi/12345SEED_3QC_9SC_4BC_0.05R_14J.txt
        python Algorithms_Main.py 3opt  instances_comp_gurobi/12345SEED_3QC_9SC_4BC_0.05R_14J.txt 3
        python Algorithms_Main.py gurobi instances_comp_gurobi/12345SEED_3QC_9SC_4BC_0.05R_14J.txt
    """
    if len(sys.argv) < 3:
        print("Usage: python Algorithms_Main.py METHOD INSTANCE_FILE [SEED]", file=sys.stderr)
        print("METHOD ∈ {grasp, vns, vnd, 3opt, gurobi}", file=sys.stderr)
        sys.exit(1)

    method = sys.argv[1].lower()
    instance_name = sys.argv[2]

    if not os.path.exists(instance_name):
        print(f"ERROR: instance file not found: {instance_name}", file=sys.stderr)
        sys.exit(1)

    # Seed is only relevant for stochastic methods; default = 1
    seed = int(sys.argv[3]) if len(sys.argv) >= 4 else 1

    return method, instance_name, seed


# ========================================= Main dispatch =============================================================

if __name__ == "__main__":
    method, instance_name, seed = parse_args()
    # ------------------------- GRASP -------------------------
    if method == "grasp":
        grasp_run = Grasp(instance_name)
        (
            best_solution_grasp,
            greedy_value_grasp,
            ls_obj_grasp,
            ls_time_grasp,
            best_solution_found_time_grasp,
            grasp_total_time,
            grasp_obj_final,
        ) = grasp_run.run(seed_try=seed)

        # Minimal, CSV-ish output for the cluster
        print(
            f"{instance_name},GRASP,{seed},"
            f"{greedy_value_grasp},"
            f"{ls_time_grasp:.4f},"
            f"{ls_obj_grasp},"
            f"{best_solution_found_time_grasp:.4f},"
            f"{grasp_total_time:.4f},"
            f"{grasp_obj_final}"

        )

    # ------------------------- VNS -------------------------
    elif method == "vns":
        vns_run = B_VNS(instance_name)
        (
            best_solution_vns,
            greedy_value_vns,
            vndls_obj_val,
            vndls_time,
            best_solution_found_time_vns,
            vns_total_time,
            vns_obj_final,
        ) = vns_run.run(seed_try=seed)

        print(
            f"{instance_name},VNS,{seed},"
            f"{greedy_value_vns},"
            f"{vndls_time:.4f},"
            f"{vndls_obj_val},"
            f"{best_solution_found_time_vns:.4f},"
            f"{vns_total_time:.4f},"
            f"{vns_obj_final}"

        )

    # ------------------------- VND (deterministic, no seed needed) -------------------------
    elif method == "vnd":
        vnd_run = VND(instance_name)
        greedy_value_vnd, vnd_result, end_vnd_time = vnd_run.run()

        print(
            f"{instance_name},VND,"
            f"{greedy_value_vnd},"
            f"{end_vnd_time:.4f},"
            f"{vnd_result}"
        )

    # ------------------------- CVND (deterministic, no seed needed) -------------------------
    elif method == "cvnd":
        vnd_run = CVND(instance_name)
        greedy_value_vnd, vnd_result, end_vnd_time = vnd_run.run()

        print(
            f"{instance_name},CVND,"
            f"{greedy_value_vnd},"
            f"{end_vnd_time:.4f},"
            f"{vnd_result}"
        )

    # ------------------------- 3-opt (Kress) -------------------------
    elif method in ("3opt", "k3opt", "threeopt"):
        problem3opt = M.MSCRBProblem()
        problem3opt.read_from_file(instance_name)
        solution3opt = MSCRBSolution(problem3opt)
        solution3opt.greedy_kress_etal()
        greedy_kopt = solution3opt.objective_function
        k_opt_run = k_opt_kress_etal(solution3opt)
        k_opt_obj_final, k_opt_time = k_opt_run.run(seed_try=seed)

        print(
            f"{instance_name},3OPT,{seed},"
            f"{greedy_kopt},"
            f"{k_opt_time:.4f},"
            f"{k_opt_obj_final}"
        )

    # ------------------------- Gurobi MIP -------------------------
    elif method == "gurobi":
        problem_gurobi = M.MSCRBProblem()
        problem_gurobi.read_from_file(instance_name)
        solution_gurobi = MSCRBSolution(problem_gurobi)
        solution_gurobi.Gurobi()

        gurobi_time = solution_gurobi.gurobi_time
        gurobi_obj = solution_gurobi.objective_function
        gurobi_status = solution_gurobi.gurobi_status
        gurobi_gap = solution_gurobi.gurobi_gap

        print(
            f"RESULT, Gurobi,"
            f"{instance_name},"
            f"{gurobi_obj},"
            f"{gurobi_status},"
            f"{gurobi_gap},"
            f"{gurobi_time:.4f}"
        )

    else:
        print(f"ERROR: unknown method '{method}'. Use one of: grasp, vns, vnd, 3opt, gurobi.", file=sys.stderr)
        sys.exit(1)
