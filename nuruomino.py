# nuruomino.py: Template para implementação do projeto de Inteligência Artificial 2024/2025.
# Devem alterar as classes e funções neste ficheiro de acordo com as instruções do enunciado.
# Além das funções e classes sugeridas, podem acrescentar outras que considerem pertinentes.

# Grupo 51:
# 1109371 Catarina Pereira
# 1110223 Carolina Quinteiro

# Imports necessários
from sys import stdin
from search import Problem
from search import Node
from search import depth_first_tree_search
from search import depth_first_graph_search
from search import depth_limited_search
from search import astar_search

# Definição das peças tetraminós e suas rotações/reflexos

# Peça L
L = [
    [[1, 0],
     [1, 0],
     [1, 1]],
    [[1, 1, 1],
     [1, 0, 0]],
    [[1, 1],
     [0, 1],
     [0, 1]],
    [[0, 0, 1],
     [1, 1, 1]],
    [[1, 1, 1],
     [0, 0, 1]],
    [[1, 0, 0],
     [1, 1, 1]],
    [[1, 1],
     [1, 0],
     [1, 0]],
    [[0, 1],
     [0, 1],
     [1, 1]]
]

# Peça I
I = [
    [[1],
     [1],
     [1],
     [1]],
    [[1, 1, 1, 1]]
]

# Peça T
T = [
    [[1, 1, 1],
     [0, 1, 0]],
    [[1, 0],
     [1, 1],
     [1, 0]],
    [[0, 1, 0],
     [1, 1, 1]],
    [[0, 1],
     [1, 1],
     [0, 1]]
]

# Peça S
S = [
    [[0, 1, 1],
     [1, 1, 0]],
    [[1, 0],
     [1, 1],
     [0, 1]],
    [[1, 1, 0],
     [0, 1, 1]],
    [[0, 1],
     [1, 1],
     [1, 0]]
]

# Junta todas as peças e variantes numa lista
ALL_PIECES = [
    ("L", L),
    ("I", I),
    ("T", T),
    ("S", S)
]

class NuruominoState:
    """Representação de um estado do Puzzle Nuruomino."""
    state_id = 0

    def __init__(self, board, blocked=False):
        self.board = board
        self.id = NuruominoState.state_id
        NuruominoState.state_id += 1
        self.blocked = blocked

    def __lt__(self, other):
        """ Este método é utilizado em caso de empate na gestão da lista
        de abertos nas procuras informadas. """
        return self.id < other.id

class Board:
    """Representação interna de um tabuleiro do Puzzle Nuruomino."""

    def __init__(self, board: list, regions=None, region_cells=None, done_regions=None, region_adjacency_graph=None, possible_placements=None, frontier_adjacency_graph=None, simple_checked=False):
        """Inicializa o tabuleiro com a matriz fornecida e com as informações das regiões."""
        self.board = board
        self.size = len(board)
        self.simple_checked = simple_checked

        if regions is not None:
            self.regions = regions
            self.region_cells = region_cells
            self.region_adjacency_graph = region_adjacency_graph
            self.done_regions = done_regions
            self.possible_placements = possible_placements
            self.frontier_adjacency_graph = frontier_adjacency_graph
        else:
            self.regions = self.get_all_regions()
            self.region_cells = {region: self.compute_cells_in_region(region) for region in self.regions}
            self.region_adjacency_graph = {region: self.adjacent_regions(region) for region in self.regions}
            self.done_regions = set(self.filled_regions())
            self.possible_placements = {}
            self.frontier_adjacency_graph = self.compute_region_frontiers()

    def adjacent_regions(self, region: int) -> list:
        """Devolve uma lista das regiões que fazem fronteira com a região enviada no argumento."""
        adj = set()
        for r in range(self.size):
            for c in range(self.size):
                if self.get_value(r, c) == region:
                    for dr in [-1, 0, 1]:
                        for dc in [-1, 0, 1]:
                            if dr == 0 and dc == 0:
                                continue
                            nr, nc = r + dr, c + dc
                            if 0 <= nr < self.size and 0 <= nc < self.size:
                                neighbour_region = self.get_value(nr, nc)
                                if neighbour_region != region and neighbour_region not in adj:
                                    adj.add(neighbour_region)
        return list(adj)

    def adjacent_positions(self, row:int, col:int) -> list:
        """Devolve as posições adjacentes à região, em todas as direções, incluindo diagonais."""
        adj_positions = []
        for dr in [-1, 0, 1]:
            for dc in [-1, 0, 1]:
                if dr == 0 and dc == 0:
                    continue
                nr, nc = row + dr, col + dc
                if 0 <= nr < self.size and 0 <= nc < self.size:
                    adj_positions.append([nr, nc])
        return adj_positions

    def adjacent_values(self, row:int, col:int) -> list:
        """Devolve os valores das celulas adjacentes à região, em todas as direções, incluindo diagonais."""
        adj_values = []
        for dr in [-1, 0, 1]:
            for dc in [-1, 0, 1]:
                if dr == 0 and dc == 0:
                    continue
                nr, nc = row + dr, col + dc
                if 0 <= nr < self.size and 0 <= nc < self.size:
                    adj_values.append(self.get_value(nr, nc))
        return adj_values

    def get_value(self, row:int, col:int) -> str:
        """Devolve o valor da célula."""
        return self.board[row][col]

    def get_region(self, row:int, col:int) -> int:
        """Devolve a região a que pertence a célula."""
        for region, cells in self.region_cells.items():
            if [row, col] in cells:
                return region
        return None

    def is_filled(self, cell) -> bool:
        """Verifica se a célula está preenchida com um tetraminó válida."""
        r, c = cell
        if self.get_value(r,c)  in ['L', 'I', 'T', 'S']:
            return True
        return False

    def is_connected_to_all_regions_inclusive(self, region):
        """Verifica se a nova peça conecta com todas as regiões já preenchidas, incluindo a nova região."""

        all_regions = set(self.frontier_adjacency_graph.keys())
        visited = set(self.done_regions)
        to_visit = list(self.done_regions)

        # Se não há regiões preenchidas, qualquer peça é válida
        if not self.done_regions:
            return True

        # Considera a nova região como preenchida e conecta-a
        visited.add(region)
        to_visit.append(region)

        # BFS para propagar conectividade entre regiões
        while to_visit:
            current = to_visit.pop()
            for neighbor in self.frontier_adjacency_graph.get(current, {}):
                if neighbor not in visited:
                    visited.add(neighbor)
                    to_visit.append(neighbor)

        unreachable = all_regions - visited
        if unreachable:
            return False

        return True

    def set_value(self, row:int, col:int, value:str):
        """Define o valor da célula."""
        self.board[row][col] = value

    def get_all_regions(self) -> set:
        """Devolve um conjunto com todos os valores das regiões do tabuleiro."""
        regions = set()
        for row in self.board:
            for value in row:
                if value not in ['L', 'I', 'T', 'S']:
                    regions.add(value)
        return regions

    def compute_cells_in_region(self, region_id: int) -> list:
        """"Calcula a lista com as coordenadas das células que pertencem à região com o id fornecido."""
        region_cells = []
        for r in range(self.size):
            for c in range(self.size):
                if self.get_value(r, c) == region_id:
                    region_cells.append([r,c])
        return region_cells

    def compute_region_frontiers(self):
        """"Devolve um dicionário com as fronteiras de cada região, ou seja, as células adjacentes a regiões diferentes."""
        frontiers = {region: {} for region in self.regions}
        for region in self.regions:
            for r, c in self.region_cells[region]:
                for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < self.size and 0 <= nc < self.size:
                        neighbour_region = self.get_value(nr, nc)
                        if neighbour_region != region and neighbour_region in self.regions:
                            if neighbour_region not in frontiers[region]:
                                frontiers[region][neighbour_region] = set()
                            frontiers[region][neighbour_region].add((nr, nc))
        return frontiers

    def get_region_cells(self, region_id: int) -> list:
        """Devolve uma lista com as coordenadas das células que pertencem à região com o id fornecido."""
        return self.region_cells[region_id]

    def filled_regions(self) -> set:
        """Devolve todas as regiões já preenchidas do tabuleiro."""
        filled = set()
        for region in self.regions:
            cells = self.get_region_cells(region)
            for cell in cells:
                if self.get_value(*cell) in ['L', 'I', 'T', 'S']:
                    filled.add(region)
                    break
        return filled

    def simple_regions(self) -> list:
        """Devolve uma lista com as regiões simples do tabuleiro (onde só cabe uma peça)."""

        simple_regions = []
        for region in self.regions:
            count = 0
            for r in range(self.size):
                for c in range(self.size):
                    if self.get_value(r, c) == region:
                        count += 1
            if count == 4:
                simple_regions.append(region)
        return simple_regions

    def identify_piece(self, region_cells):
        """Retorna o nome da peça ('L', 'I', 'T', 'S') se corresponder a alguma variante, ou None."""
        # Normaliza as posições para começar em (0,0)
        min_r = min(r for r, c in region_cells)
        min_c = min(c for r, c in region_cells)
        norm_cells = sorted([[r - min_r, c - min_c] for r, c in region_cells])

        # Cria uma matriz 0/1 representando a região
        max_r = max(r for r, c in norm_cells)
        max_c = max(c for r, c in norm_cells)
        shape = [[0 for _ in range(max_c + 1)] for _ in range(max_r + 1)]
        for r, c in norm_cells:
            shape[r][c] = 1

        # Compara com todas as variantes das peças
        for name, variants in ALL_PIECES:
            for variant in variants:
                if shape == variant:
                    return name
        return None

    def get_piece_variants(self, piece_name):
        """Devolve todas as variantes da peça."""
        for name, variants in ALL_PIECES:
            if name == piece_name:
                return variants
        return []

    def possible_tetra_placements(self, region_id, piece) -> list:
        """Devolve uma lista de todas as possíveis colocações de uma peça na região especificada."""

        key = (region_id, piece)
        if key in self.possible_placements:
            return self.possible_placements[key]

        region_cells = self.get_region_cells(region_id)
        region_set = set(tuple(cell) for cell in region_cells)
        piece_variants = self.get_piece_variants(piece)
        placements = []
        region_rows = []
        region_cols = []

        # Limites da região
        for cell in region_cells:
            region_rows.append(cell[0])
            region_cols.append(cell[1])
        min_r, max_r = min(region_rows), max(region_rows)
        min_c, max_c = min(region_cols), max(region_cols)

        for shape in piece_variants:
            height = len(shape)
            width = len(shape[0])
            for dr in range(min_r, max_r - height + 2):
                for dc in range(min_c, max_c - width + 2):
                    shape_cells = []
                    valid = True
                    for i in range(height):
                        for j in range(width):
                            if shape[i][j]:
                                cell = [dr + i, dc + j]
                                if tuple(cell) not in region_set:
                                    valid = False
                                    break
                                shape_cells.append(cell)
                        if not valid:
                            break
                    if valid:
                        placements.append(shape_cells)

        self.possible_placements[key] = placements
        return placements

    def possible_region_placements(self, region_id) -> list:
        """Devolve uma lista de todas as possíveis colocações de peças na região especificada, por peça."""
        all_placements = []
        for piece_name, _ in ALL_PIECES:
            placements = self.possible_tetra_placements(region_id, piece_name)
            all_placements.append((piece_name, placements))

        return all_placements

    def placements_with_connections(self, region_id, placements) -> list:
        """"Verifica se as colocações de peças na região especificada estão conectadas às regiões adjacentes já preenchidas."""
        adj = self.region_adjacency_graph[region_id]
        filled = self.done_regions
        connected = []

        if all(a in filled for a in adj):
            for placement in placements:
                found = False
                for [r, c] in placement:
                    for dr, dc in [(-1,0), (1,0), (0,-1), (0,1)]:
                        nr, nc = r + dr, c + dc
                        if 0 <= nr < self.size and 0 <= nc < self.size and self.get_value(nr, nc) in ['L', 'I', 'T', 'S']:
                            connected.append(placement)
                            found = True
                            break
                    if found:
                        break
            return connected

        region_cells = self.get_region_cells(region_id)
        for placement in placements:
            side = self.side_adjacents(placement)
            if all(a in region_cells for a in side):
                pass
            else:
                connected.append(placement)
        return connected

    def fill_simple_regions(self):
        """Preenche automaticamente as regiões simples (com 4 células) com a peça correspondente, se possível."""
        simple = self.simple_regions()
        for region in simple:
            cells = self.get_region_cells(region)
            piece_name = self.identify_piece(cells)
            if piece_name is not None:
                # Preenche a região com o nome da peça
                for r, c in cells:
                    self.set_value(r, c, piece_name)
                self.done_regions.add(region)

    def side_adjacents(self, tetra:list) ->list:
        """Devolve as células adjacentes à peça, excluindo diagonais."""
        n = self.size
        adj = []
        for [r, c] in tetra:
            if 0 <= r + 1 < n and [r + 1, c] not in tetra:
                adj.append([r + 1, c])
            if 0 <= c - 1< n and [r, c - 1] not in tetra:
                adj.append([r, c - 1])
            if 0 <= c + 1 < n and [r, c + 1] not in tetra:
                adj.append([r, c + 1])
            if 0 <= r - 1 < n and [r-1,c] not in tetra:
                adj.append([r - 1, c])
        return adj

    def get_cell_values(self, cells:list) -> list:
        """Devolve os valores das células dadas."""
        adj = []
        for [r, c] in cells:
            adj.append(self.get_value(r, c))
        return adj

    def forms_square(self, piece_cells) -> bool:
        """Verifica se ao colocar uma peça nas posições piece_cells se forma algum quadrado 2x2."""
        piece_names = [name for name, _ in ALL_PIECES]
        for r, c in piece_cells:
            # Verifica os 4 possíveis quadrados 2x2 em que (r, c) pode estar
            for dr, dc in [(0, 0), (-1, 0), (0, -1), (-1, -1)]:
                square = []
                for i in [0, 1]:
                    for j in [0, 1]:
                        nr, nc = r + dr + i, c + dc + j
                        if 0 <= nr < self.size and 0 <= nc < self.size:
                            # Considera preenchido se está em piece_cells ou já tem peça no tabuleiro
                            if [nr, nc] in piece_cells or self.get_value(nr, nc) in piece_names:
                                square.append((nr, nc))
                if len(square) == 4:
                    return True
        return False

    def is_valid_tetramino(self, tetra: list) -> bool:
        """Verifica se colocar a peça é válido, ou seja, não forma quadrados 2x2 e não tem adjacentes iguais."""

        piece = self.identify_piece(tetra)
        adj = self.side_adjacents(tetra)
        adj_values = self.get_cell_values(adj)
        if piece in adj_values:
            return False

        if self.forms_square(tetra):
            return False

        region = self.get_region(*tetra[0])
        if self.bfs_reach_all_from(region):
            return True

        return False

    def valid_pieces(self, pieces: list) -> list:
        """Devolve uma lista com as peças tetraminós válidas, ou seja, que não formam quadrados 2x2 e não têm adjacentes iguais."""
        new =[]
        for l in pieces:
            if self.is_valid_tetramino(l):
                new.append(l)
        return new

    def print_instance(self):
        """Imprime o tabuleiro no formato especificado no enunciado."""
        for i, row in enumerate(self.board):
            end = "\n" if i < len(self.board) - 1 else ""
            print("\t".join(row), end=end)

    def one_path(self) -> bool:
        """Verifica se o tabuleiro forma um unico caminho"""
        piece_names = [name for name, _ in ALL_PIECES]
        visited = set()
        total_filled = 0

        # Encontrar uma célula ocupada por peça
        start = None
        for r in range(self.size):
            for c in range(self.size):
                if self.get_value(r, c) in piece_names:
                    total_filled += 1
                    if start is None:
                        start = (r, c)

        if start is None:
            return False  # Não há peças, tecnicamente está "conectado"

        # BFS/DFS para visitar todas as células ocupadas
        stack = [start]
        while stack:
            r, c = stack.pop()
            if (r, c) in visited:
                continue
            visited.add((r, c))
            for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < self.size and 0 <= nc < self.size:
                    if self.get_value(nr, nc) in piece_names and (nr, nc) not in visited:
                        stack.append((nr, nc))

        return len(visited) == total_filled

    def bfs_reach_all_from(self, start_region):
        """Verifica se é possível atingir todas as regiões a partir de start_region via frontier_adjacency_graph."""
        visited = set()
        queue = [start_region]

        while queue:
            current = queue.pop(0)
            if current in visited:
                continue
            visited.add(current)
            neighbors = self.frontier_adjacency_graph.get(current, {})
            for neighbor in neighbors:
                if neighbor not in visited:
                    queue.append(neighbor)

        # Verifica se todas as regiões estão acessíveis
        return visited == self.regions

    def update_frontiers(self, region, cells):
        """ Atualiza o frontier_adjacency_graph da região 'region' após colocar uma peça nas células 'cells'."""

        new_frontiers = {}  # mapa {vizinha: set de células da fronteira}
        cells_set = set(tuple(cell) for cell in cells)

        new_adj = self.side_adjacents(cells)  # células diretamente ao lado da peça

        for r, c in new_adj:
            neighbour_reg = self.get_region(r, c)
            if neighbour_reg != region:
                if neighbour_reg not in new_frontiers:
                    new_frontiers[neighbour_reg] = set()
                new_frontiers[neighbour_reg].add((r, c))

        # Atualiza a entrada da região principal
        self.frontier_adjacency_graph[region] = new_frontiers

        # Também atualiza o inverso: as regiões vizinhas apontam de volta para esta
        old_frontiers= self.frontier_adjacency_graph[region]
        for neighbour in old_frontiers:
            if neighbour not in new_frontiers :
                if region in self.frontier_adjacency_graph.get(neighbour, {}):
                    del self.frontier_adjacency_graph[neighbour][region]

            else:
                c = self.frontier_adjacency_graph[neighbour].get(region, set())
                comuns=c.intersection(cells_set)
                self.frontier_adjacency_graph[neighbour][region]= comuns

    @staticmethod
    def parse_instance():
        """Lê o test do standard input (stdin) que é passado como argumento
        e retorna uma instância da classe Board.

        Por exemplo:
            $ python3 pipe.py < test-01.txt

            > from sys import stdin
            > line = stdin.readline().split()
        """

        board = []
        for line in stdin:
            board.append(list(line.strip().split()))

        return Board(board)

class Nuruomino(Problem):
    """Problema Nuruomino, que herda da classe Problem."""

    def __init__(self, board: Board):
        """O construtor especifica o estado inicial."""
        self.board = board
        self.initial = NuruominoState(board)

    def actions(self, state: NuruominoState):
        """ Retorna uma lista de ações que podem ser executadas a partir do estado passado como argumento. """

        if state.blocked:
            return []

        board = state.board
        filled = board.done_regions

        # Se não há regiões preenchidas
        if not filled:
            if not board.simple_checked:
                board.fill_simple_regions()
                board.simple_checked = True
                candidate_regions = [r for r in board.regions if r not in board.done_regions]
            else:
                candidate_regions = board.regions
        else:
            # Só regiões adjacentes a regiões preenchidas
            candidate_regions = set()
            for region in filled:
                candidate_regions.update(board.region_adjacency_graph[region])
            candidate_regions = [r for r in candidate_regions if r not in filled]

        # Calcula o número de possibilidades para cada região ainda não preenchida
        region_actions = {}
        for region in candidate_regions:
            if region in board.done_regions:
                continue
            actions = []
            piece_names_set = set()
            for piece_name, _ in ALL_PIECES:
                placements = board.valid_pieces(board.possible_tetra_placements(region, piece_name))
                for p in placements:
                    actions.append((piece_name, p))
                    piece_names_set.add(piece_name)

            if not actions:
                return []

            adj_count = len(board.region_adjacency_graph[region])
            region_actions[region] = {'actions': actions, 'adj_count': adj_count, 'piece_names': list(piece_names_set)}
            if len(actions) == 1:
                piece_name, placement = actions[0]
                return [(region, piece_name, placement)]

        # Ordena as regiões pelo menor número de ações possíveis, número de adjacentes e número de peças
        sorted_regions = sorted(
            region_actions.items(),
            key=lambda x: (len(x[1]['actions']), x[1]['adj_count'], len(x[1]['piece_names']))
        )

        # Se alguma região só tem uma possibilidade, devolve logo essa ação
        if sorted_regions and len(sorted_regions[0][1]['actions']) == 1:
            region = sorted_regions[0][0]
            piece_name, placement = sorted_regions[0][1]['actions'][0]
            return [(region, piece_name, placement)]

        # Caso contrário, devolve todas as ações possíveis da região mais restrita
        if sorted_regions:
            region, info = sorted_regions[0]
            return [(region, piece_name, placement) for piece_name, placement in info['actions']]

        return []

    def result(self, state: NuruominoState, action):
        """Retorna o estado resultante de executar a 'action' sobre
        'state' passado como argumento. A ação a executar deve ser uma
        das presentes na lista obtida pela execução de
        self.actions(state)."""

        region, piece_name, cells = action

        new = [row[:] for row in state.board.board]

        for r, c in cells:
            new[r][c] = piece_name

        new_done_regions = set(state.board.done_regions)
        new_done_regions.add(region)

        new_possible_placements = {k: v.copy() for k, v in state.board.possible_placements.items()}

        new_frontier_adjacency_graph = {
            k: {kk: vv.copy() for kk, vv in v.items()}
            for k, v in state.board.frontier_adjacency_graph.items()
        }

        new_board = Board(new, state.board.regions, state.board.region_cells, new_done_regions, state.board.region_adjacency_graph, new_possible_placements, new_frontier_adjacency_graph, simple_checked=state.board.simple_checked)

        new_board.update_frontiers(region, cells)
        if not new_board.bfs_reach_all_from(region):
            return NuruominoState(new_board, blocked=True)

        for reg in new_board.region_adjacency_graph[region]:
            if reg not in new_board.done_regions:
                possible = 0
                for pname, _ in ALL_PIECES:
                    valid_placements = new_board.valid_pieces(new_board.possible_tetra_placements(reg, pname))
                    new_board.possible_placements[(reg, pname)] = valid_placements
                    possible += len(valid_placements)
                if possible == 0:
                    return NuruominoState(new_board, blocked=True)

        return NuruominoState(new_board)

    def goal_test(self, state: NuruominoState):
        """Testa se o estado é um estado objetivo."""

        if state.blocked:
            return False

        if len(state.board.done_regions) != len(state.board.regions):
            return False

        if not state.board.one_path():
            return False

        return True


    def h(self, node: Node):
        """ Função heuristica utilizada para a procura A*."""
        board = node.state.board
        piece_names = [name for name, _ in ALL_PIECES]

        regions_left = len(board.regions) - len(board.done_regions)
        empty_cells = 0
        min_poss = float('inf')
        sum_poss = 0
        blocked = False
        critical_regions = 0  # count regions with very few options (<=2)

        # Count empty cells (cells not assigned a piece name)
        for r in range(board.size):
            for c in range(board.size):
                if board.get_value(r, c) not in piece_names:
                    empty_cells += 1

        # For each unfinished region, count the number of possible placements
        for region in board.regions:
            if region not in board.done_regions:
                possible = 0
                for piece_name, _ in ALL_PIECES:
                    valid_placements = board.valid_pieces(board.possible_tetra_placements(region, piece_name))
                    possible += len(valid_placements)

                if possible == 0:
                    blocked = True  # no valid placements for this region, dead end
                if 0 < possible <= 2:
                    critical_regions += 1  # regions with very few options are risky

                min_poss = min(min_poss, possible)
                sum_poss += possible

        if blocked:
            return float('inf')  # blocked state, no solution from here

        heuristic = (
            5 * regions_left +
            (empty_cells / 4.0) +
            3 * (1 if min_poss == float('inf') else min_poss) +
            4 * critical_regions +
            (sum_poss / max(1, regions_left))
        )
        return heuristic


board_ex = Board.parse_instance()
problem = Nuruomino(board_ex)
state_ex = NuruominoState(board_ex)
goal_node = depth_first_tree_search(problem)
#board_ex.print_instance()
#print("Goal?", problem.goal_test(goal_node.state))
goal_node.state.board.print_instance()
