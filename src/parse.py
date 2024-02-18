import json
import os
import networkx as nx
import random
import copy
import itertools
import errno
import functools
import signal

class TimeoutError(Exception):
    pass

def timeout(seconds=10, error_message=os.strerror(errno.ETIME)):
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result

        return wrapper

    return decorator

def construct_graph(report):
    G = nx.DiGraph()

    for entity_name, entity_info in report['entities'].items():
        G.add_node(entity_name, **entity_info)
        
        for relation in entity_info['relations']:
            # assert relation[0] == 'located_at'
            G.add_edge(entity_name, relation[1], relation=relation[0])
    
    return G

def structure_match_helper(G1, G2, t1, t2, g1tog2, g2tog1):

    if not t2 in g1tog2[t1]:
        return False
    
    # leaf nodes comparison
    if G1.out_degree[t1] == 0 and G2.out_degree[t2] == 0:
        return True

    # Only one of them is leaf node:
    if G1.out_degree[t1] > 0 and G2.out_degree[t2] == 0:
        return False
    
    if G1.out_degree[t1] == 0 and G2.out_degree[t2] > 0:
        return False

    # Both are trees
    children1 = G1[t1]
    children2 = G2[t2]

    structure_same_childs = {}

    if not len(children1) == len(children2):
        return False
    
    for child1 in children1:
        rel_type_1 = G1[t1][child1]
        possible_child2_ls = g1tog2[child1]

        # Check whether two child trees are the same
        for possible_child2 in possible_child2_ls:
            if possible_child2 in children2:
                rel_type_2 = G2[t2][possible_child2]
                if rel_type_1 == rel_type_2:
                    subtree_is_same = structure_match_helper(G1, G2, child1, possible_child2, g1tog2, g2tog1)
                    if subtree_is_same: 
                        if not child1 in structure_same_childs:
                            structure_same_childs[child1] = []
                        structure_same_childs[child1].append(possible_child2)
    
    # Assert all of the structurely same child only have one correspondance for right now.
    mapped_children2 = []
    all_structure_same_mappings = None
    maps = get_all_maps(structure_same_childs, children1, children2)

    while True:
        try:
            m = next(maps)
        except StopIteration:
            break
        if check_bijection(mapping=m, from_space=children1, to_space=children2):
            all_structure_same_mappings = m 
            break     

    if all_structure_same_mappings is None:
        return False
        
    return True

@timeout(5)  
def compare_graphs(G1, G2):
    g1tog2 = {}
    g2tog1 = {}
    no_matches = []

    # Check the basic equvalency of token and labels
    for n1 in G1.nodes():
        no_match = True
        for n2 in G2.nodes():
            if G1.nodes[n1]['tokens'] == G2.nodes[n2]['tokens'] and \
               G1.nodes[n1]['label'] == G2.nodes[n2]['label']:
                if not n1 in g1tog2:
                    g1tog2[n1] = []
                if not n2 in g2tog1:
                    g2tog1[n2] = []
                g1tog2[n1].append(n2)
                g2tog1[n2].append(n1)
                no_match = False
        if no_match:
            no_matches.append(n1)

    if not len(no_matches) == 0:
        return False
        
    # Check the structure to verify the rest
    roots1 = [n for n,d in G1.in_degree() if d==0] 
    roots2 = [n for n,d in G2.in_degree() if d==0] 

    sm_g1tog2 = {}
    sm_g2tog1 = {}

    root_match = {}
    # Compare each tree in the forest
    for root1 in roots1:
        # Check each possible match 
        for root2 in g1tog2[root1]:
            is_same = structure_match_helper(G1, G2, root1, root2, g1tog2, g2tog1)
            if is_same:
                if not root1 in root_match:
                    root_match[root1] = []
                root_match[root1].append(root2)

    all_single_maps = get_all_maps(mapping=root_match, from_space=roots1, to_space=roots2)
    is_bijection = False


    while True:
        try:
            m = next(all_single_maps)
        except StopIteration:
            break
        is_bijection = check_bijection(mapping=m, from_space=roots1, to_space=roots2)
        if is_bijection:
            break
    
    return is_bijection

def check_bijection(mapping, from_space, to_space):

    to_space = set(to_space)
    # single_maps = get_all_maps(mapping=mapping)
    is_valid = False
    
    all_tos = set()
    for e1 in from_space:

        if not e1 in mapping:
            return False
        
        e2 = mapping[e1]
        if not e2 in to_space:
            return False
        
        all_tos.add(e2)

    if len(all_tos) == len(to_space):
        return True
            
    return False

def product_without_dupl(*args, repeat=1):
    pools = [tuple(pool) for pool in args] * repeat
    result = [[]]
    for pool in pools:
        result = [x+[y] for x in result for y in pool if y not in x] # here we added condition
    result = set(list(map(lambda x: tuple(sorted(x)), result))) # to remove symmetric duplicates
    for prod in result:
        yield tuple(prod)
        
def get_all_maps(mapping, from_space, to_space):
    # Assertion: this will generate an bijection map
    # from_space = set(mapping.keys())
    # to_space = set( v for v_ls in mapping.values() for v in v_ls)
    if not len(from_space) == len(to_space):
        return
    
    single_maps = itertools.product(*mapping.values())
    # single_maps = product_without_dupl(*mapping.values())

    for single_map in single_maps:
        yield {k: single_map[ct] for ct, k in enumerate(mapping)}

def gen_isomorphic_graph(graph):
    new_graph = nx.DiGraph()

    ori_nodes = list(graph.nodes())
    shuffled_nodes = copy.deepcopy(ori_nodes)
    random.shuffle(shuffled_nodes)

    node_lookup = {ori: new for ori, new in zip(ori_nodes, shuffled_nodes)}
    
    for node in graph.nodes():
        new_node_info = copy.deepcopy(graph.nodes[node])
        new_node_info['relations'] = []

        for ori_rela, ori_node in graph.nodes[node]['relations']:
            new_node_info['relations'].append([ori_rela, node_lookup[ori_node]])
        
        new_graph.add_node(node_lookup[node], **new_node_info)
    
    for edge in graph.edges():
        edge_info = graph[edge[0]][edge[1]]
        new_graph.add_edge(node_lookup[edge[0]], node_lookup[edge[1]], **edge_info)

    return new_graph, node_lookup


if __name__ == "__main__":
    data_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../../data'))
    pred_dir = os.path.join(data_dir, 'Radgraph')
    gt_dir = os.path.join(data_dir, 'medical_imaging')
    check_split = 'test'

    if check_split == 'train':  
        gt_data_path = os.path.join(gt_dir, 'train.json')
        pred_data_path = os.path.join(pred_dir, 'train-pred.json')
    else:
        gt_data_path = os.path.join(gt_dir, 'test.json')
        pred_data_path = os.path.join(pred_dir, 'test-pred.json')


    gt_data_points = json.load(open(gt_data_path))
    pred_data_points = json.load(open(pred_data_path))

    gt_graph_reports = {}
    all_outcomes = []
    timeout_ct = 0

    for file_name, label_info in gt_data_points.items():
        gt_graph_reports[file_name] = []
        for tag, report in label_info.items():
            # For each manual labeler, create a parse version of the report
            if 'labeler' in tag:
                G = construct_graph(report)
                gt_graph_reports[file_name].append(G)
            
            elif 'entities' in tag:
                G = construct_graph(label_info)
                gt_graph_reports[file_name].append(G)

    pred_graph_reports = {}
    for file_name, label_info in pred_data_points.items():
        pred_graph_reports[file_name] = []
        for tag, report in label_info.items():
            # For each manual labeler, create a parse version of the report
            if 'labeler' in tag:
                G = construct_graph(report)
                pred_graph_reports[file_name].append(G)

            elif 'entities' in tag:
                G = construct_graph(label_info)
                pred_graph_reports[file_name].append(G)

    
    for file_name, pred_graphs in pred_graph_reports.items():

        # if not file_name == "p15/p15024484/s55357745.txt":
        #     continue

        print(file_name)
        gt_graph = gt_graph_reports[file_name]

        # for ct1, g1 in enumerate(pred_graphs):
        #     for ct2, g2 in enumerate(gt_graphs):
        #         # iso_g2, node_lookup = gen_isomorphic_graph(g2)
        #         # iso_g1, node_lookup = gen_isomorphic_graph(g1)
        #         outcome = compare_graphs(g1, g2)
        #         print(outcome)
        # g1, node_lookup_1 = gen_isomorphic_graph(gt_graph[0])
        # g2, node_lookup_2 = gen_isomorphic_graph(gt_graph[0])

        try:
            outcome = compare_graphs(gt_graph[0], pred_graphs[0])
            all_outcomes.append(outcome)
        except:
            timeout_ct += 1
        print(outcome)

    same_ct = len([i for i in all_outcomes if i])
    different_ct =  len([i for i in all_outcomes if not i])

    print(same_ct)
    print(different_ct)
    print(timeout_ct)
    print('end')