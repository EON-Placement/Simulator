import networkx as nx
import numpy as np
import csv
import sys
import argparse
from math import trunc
from string import lower
from random import randint
from random import seed

#recebe os parametros passados
parser = argparse.ArgumentParser(description='EON_Placement')
parser.add_argument("-top", default='cost239_r', help = 'Nome da topologia desejada', type = str)
parser.add_argument("-slots", default=160, help = 'Quantidade de slots por link', type = int)
parser.add_argument("-regens", default= 50, help = 'Quatidade total de regeneradores', type = int)
parser.add_argument("-mod", default='2', help = 'Tabela de modulacao que sera utilizada', type = int)
parser.add_argument("-algo", default='od', help = 'Estrategia de RP e RA que sera utilizada' , type = str)
parser.add_argument("-sa", default='ff', help = 'Medoto de alocacao de espectro empregado', type = str)
parser.add_argument("-cam", default='k2', help = 'Politica de escolha de caminhos', type = str)
parser.add_argument("-c1", default=1, help = 'Constante 1 para calculo do custo do OD', type = int)
parser.add_argument("-c2", default=1, help = 'Constante 2 para calculo do custo do OD', type = int)
parser.add_argument("-c3", default=10, help = 'Constante 3 para calculo do custo do OD', type = int)
parser.add_argument("-c4", default=1, help = 'Constante 4 para calculo do custo do OD', type = int)
parser.add_argument("-amostra", default=0, help = 'Numero da amostra da requisicao que sera executada', type = int)
parser.add_argument("-min_bw", default=100, help = 'Valor minimo da banda das requisicoes', type = int)
parser.add_argument("-max_bw", default=400, help = 'Valor maximo da banda das requisicoes', type = int)
parser.add_argument("-reqs", default=200, help = 'Quantidade de requisicoes que serao executadas', type = int)
parser.add_argument("-taxa", default=1.0, help = 'Taxa de chegada das requisicoes', type = float)
parser.add_argument("-dur", default=360.0, help = 'Duracao media das requisicoes', type = float)
parser.add_argument("-traf", default='u', help = 'Tipo de distribuicao de trafego considerada', type = str)

args = parser.parse_args()

#bloco: variaveis globais
    #parametros (variaveis com os valores de entrada que nao sao alterados)
topologia = args.top
slots = args.slots
regens = args.regens
mod = args.mod
algo = args.algo #deve ser no padrao od, od2(faz reposicionamento), ou rp_ra
sa = args.sa
cam = args.cam
c1 = args.c1
c2 = args.c2
c3 = args.c3
c4 = args.c4
amostra_req = args.amostra
min_bw = args.min_bw
max_bw = args.max_bw
reqs = args.reqs
taxa = args.taxa
dur = args.dur
traf = args.traf
url = '/home/user/' #identifica o caminho onde esta a pasta do simulador
warmup_time = 1 #usada para identificar o momento a partir do qual as metricas serao computadas
div_espectro = 8 #usada para agrupar as demandas em dois blocos quando for usada a alocacao last-fit
modulacao1 = {0:('BPSK', 25, 3000), 1:('QPSK', 50, 1500), 2:('8-QAM', 75, 750)} #retirado do artigo de Hong Guo 2017
modulacao2 = {0:('BPSK', 12.25, 4000), 1:('QPSK', 25, 2000), 2:('8-QAM', 37.5, 1000), 3:('16-QAM', 50, 500), 4:('32-QAM', 62.5, 250)} #retirado do artigo de Krzyztof Walkowiak 2018 
modulacao3 = {0:('BPSK', 12.25, 4000), 1:('QPSK', 25, 2000), 2:('8-QAM', 37.5, 1000)} #adaptada da modulacao2 para testes

    #variaveis de processamento (usadas para guardar as informacoes do programa em memoria, sendo alteradas ao longo da execucao)
modulacao = {} #recebe a modulacao que sera usada na simulacao
G = nx.Graph() #instancia a rede como um objeto
slots_link = {} #guarda cada link da rede como um vetor que contem seus respectivos slots
info_links = {} #id_link, comprimento (identifica o link por numero e guarda seu comprimento)
req_entrantes = [] #[[instante, id_req, origem, destino, banda]] (guarda os dados de entrada do arquivo de requisicoes)
req_processadas = [] #[[no_regen],[[id_links], (inicio, fim)]] (guarda o estado atual da rede apos o processamento de cada requisicao)
rpa = [] #recebe quantidade de regeneradores livres em cada no
estoque_regens = regens #guarda a quantidade de regeneradores disponivel em estoque para o OD
estoque_nao_usado = regens #guarda a quantidade de regeneradores nao usados 
req_block = 0 #contabiliza as requisicoes bloqueadas
banda_block = 0 #contabiliza a banda bloqueda
banda_total = 0 #contabiliza a banda total
hops_total = 0 #contabiliza o numero total de saltos que foram dados pelas requisicoes atendidas
aux_max_regens_usados = [] #auxilia no computo do maximo de regeneradores usados simultaneamente
todos_caminhos_links = [] #guarda todos os caminhos possiveis na rede, considerando a politica de caminhos em vigor
fragmentacao_cada_caminho = [] #guarda o valor da fragmentacao de cada caminho ao longo da simulacao
links_frag = [] #guarda os links que precisam ser considerados no proximo calculo da fragmentacao da rede (usado para as alteracoes na rede decorrentes da saida de uma requisicao em vigor)
w = 0 #guarda o valor do peso de cada caminho que sera considerado no momento do calculo da fragmentacao
frag_max = 0 #guarda o valor da maior quantidade de slots contiguos que eh considerado fragmento (onde a menor demanda possivel nao pode ser alocada)
warmup_req = 0 #guarda o valor da primeira requisicao que sera considerada no calculo do bloqueio, em decorrencia do warmup_time
rp = 'none' #guarda a politica de posicionamento de regenradores que sera utilizada
ra = 'none' #guarda a politica de alocacao de regeneradores que sera utilizada

    #metricas (variaveis que contem os valores que serao usados na composicao dos resultados)
primeiro_block = 0 #guarda o numero da primeira requisicao que foi bloqueada
max_regens_usados = [] #guarda o maximo de regeneradores que foram simultaneamente usados em cada no
bloq_no_origem = [] #guarda a quantidade de requisicoes que foram bloqueadas, separadas pelos nos origem
k = [0,0,0,0,0,0,0,0,0,0] #guarda a quantidade de requisicoes que foram atendidas separadas pelos caminhos da politica de caminhos

#bloco: inicializacao da rede 
def carrega_topologia(topologia): #instancia as informacoes da rede lidas no arquivo de topologia
    if topologia == 'cost239':
        arq_top = url+'EON_Placement/Topologias/cost239.csv'
    if topologia == 'cost239_r': #topologia cost239 considerando as distancias reais entre os nos
        arq_top = url+'EON_Placement/Topologias/cost239_r.csv'
    if topologia == 'nsfnet':
        arq_top = url+'EON_Placement/Topologias/nsfnet.csv'
    if topologia == 'nsfnet_r': #topologia nsfnet considerando as distancias reais entre os nos
        arq_top = url+'EON_Placement/Topologias/nsfnet_r.csv'
    if topologia == 'top_teste': #topologia criada para realizacao de testes
	arq_top = url+'EON_Placement/Topologias/top_teste.csv'
    with open(arq_top, 'rb') as topologia:
        reader = csv.reader(topologia) #le o arquivo com as informacoes da topologia
        try: 
            for linha in reader: #guarda as informacoes nas variaveis de processamento           
                if linha[0] == 'no':
                    G.add_node(int(linha[1]))
                if linha[0] == 'link':
                    G.add_edge(int(linha[1]), int(linha[2]), label = linha[3], weight = int(linha[4]))
                    info_links[int(linha[1]), int(linha[2])] = (int(linha[3]), int(linha[4]))
                    info_links[int(linha[2]), int(linha[1])] = (int(linha[3]), int(linha[4]))
        except csv.Error as e:
            sys.exit('Dados %s, linha %d: %s' % (topologia, reader.line_num, e))

def cria_slots(slots): #instancia um vetor correspondente aos slots em cada link
    for l in xrange(G.number_of_edges()):
        slot = []        
        for s in xrange(slots): 
            slot.append(0) #valor 0 indica que o slot esta livre para uso
        slots_link[l] = slot

def carrega_variaveis_vetoriais(valor_rpa): #inicializa todas as variaveis vetoriais para que tenham tamanho referente a quantidade de nos da rede
    for r in xrange(G.number_of_nodes()):
        rpa.append(valor_rpa) #valor_rpa 0 para a execucao da alocacao e 999999 para processar o posicionamento no msu 
        bloq_no_origem.append(0) 
        max_regens_usados.append(0)
        aux_max_regens_usados.append(0)      

def identifica_algoritmo(algo): #separa o posicionamento da alocacao permitindo a execucao em dois processos caso nao seja o OD
    global rp
    global ra
    if algo == 'od' or algo == 'od2': 
	if algo == 'od':        
	    rp = 'od'
	else:
	    rp = 'od2'
    else:
        rp = algo.split('_')[0]
        ra = algo.split('_')[1]

def identifica_modulacao(mod): #instancia a modulacao que sera usada na simulacao
    global modulacao
    if mod == 1:
        modulacao = modulacao1
    if mod == 2:
        modulacao = modulacao2
    if mod == 3:
        modulacao = modulacao3

#bloco: estrategia de placement (executam o posicionamento dos regeneradores na rede)
def executa_placement(rp): #identifica a politica de posicionamento e chama a execucao da mesma
    if rp == 'od' or rp == 'od2':
        cont_reqs = 0 #contabiliza as requisicoes entrantes
        for r in xrange(len(req_entrantes)): #chama a execucao do OD para cada requisicao
            if cont_reqs == reqs: 
                break #para o processamento quando a ultima requisicao entrante eh processada 
            placement_od(req_entrantes[r][0], req_entrantes[r][1], req_entrantes[r][2], req_entrantes[r][3], req_entrantes[r][4])
            cont_reqs = req_entrantes[r][1] #contabiliza as requisicoes entrantes
    if rp == 'up':
	placement_up()
    if rp == 'nd':
        placement_nd() 
    if rp == 'tw':
        placement_tw()
    if rp == 'msu':
	placement_msu()
        
def placement_up(): #distribui os regeneradores pelos nos de maneira uniforme
    n = G.number_of_nodes()
    up = regens/n
    resto = regens % n
    for i in xrange(0, n): #instancia o vetor que corresponde a quantidade de regeneradores por no
        rpa[i] = up
    if resto != 0: #quando a divisao dos regeneradores pelos nos nao eh exata, os regeneradores faltantes sao distribuidos aleatoriamente
        for i in range(0, resto):
            rand = randint(0, n-1)
            rpa[rand] = rpa[rand] + 1        

def placement_nd(): #distribui os regeneradores pelos nos em quantidade proporcional ao grau de cada no
    soma_grau = 0
    aux_nd = nx.degree(G)   
    for sg in xrange  (0, len(aux_nd)): #gera a soma de todos os graus de todos os nos da rede
        soma_grau += aux_nd[sg]   
    for n in xrange (0, len(aux_nd)): #instancia o vetor que corresponde a quantidade de regeneradores por no
        rpa[n] = regens * aux_nd[n] / soma_grau 
    resto = regens - sum(rpa) 
    if resto > 0:  #quando a divisao dos regeneradores pelos nos nao e exata, os regeneradores faltantes sao distribuidos aleatoriamente
        for r in xrange (0, resto):
            rand = randint(0, n-1)
            rpa[rand] = rpa[rand] + 1
   
def placement_tw(): #distribui os regeneradores pelos nos em quantidade proporcional ao numero de menores caminhos que passam por cada no
    aux_tw1 = []
    for i in xrange(0, G.number_of_nodes()): #cria o vetor que recebera a quantidade de caminhos que atravessam cada no
        aux_tw1.append(0)
    aux_tw = dict(nx.all_pairs_shortest_path(G)) #calcula todos os menores caminhos da rede
    for l  in aux_tw: #para cada caminho que tenha pelo menos 3 nos: retira a origem e o destino e identifica os nos que foram atravessados pelo caminho salvando a informacao no vetor aux_tw1
        for c in aux_tw[l]:
            if len(aux_tw[l][c]) > 2:
                for n in xrange(1, len(aux_tw[l][c])-1):
                    aux_tw1[aux_tw[l][c][n]] +=1 
    soma_tw = sum (aux_tw1) #gera a soma de todos os caminhos que atravessaram todos os nos da rede
    for st in  xrange(0, len(aux_tw1)): #instancia o vetor que corresponde a quantidade de regeneradores por no
        rpa[st] = regens * aux_tw1[st] / soma_tw
    resto = regens - sum(rpa)
    if resto > 0: #quando a divisao dos regeneradores pelos nos nao eh exata, os regeneradores faltantes sao distribuidos aleatoriamente
        for  r in xrange(0, resto):
            rand = randint(0, len(aux_tw1)-1)
            rpa[rand] = rpa[rand] + 1       

def placement_msu(): #distribui os regeneradores pelos nos em quantidade proporcional ao maior numero de regeneradores simultaneamente utilizados que seriam necessarios para atender as demandas, caso a quantidade de regeneradoers fosse infinita (999999)
    global req_block 
    global banda_block
    global banda_total
    global hops_total 
    global max_regens_usados
    global req_processadas
    global aux_max_regens_usados
    global bloq_no_origem
    global ocupacao_rede
    global ocupacao_links
    global k
    global indice_fragmentacao
    global fragmentacao_cada_caminho
    global bloq_parcial
    global primeiro_block
    global warmup_req
    executa_assignment(ra) #executa a politica de alocacao considerando que ha infinitos regeneradores em cada no
    num_nos = len(max_regens_usados) 
    soma_msu =  sum(max_regens_usados) #calcula o numero maximo de regeneradores que foram simultaneamente utilizados 
    for n in xrange(0, num_nos): #instancia o vetor que corresponde a quantidade de regeneradores por no
	rpa[n] = int(round(regens * max_regens_usados[n]/max(float(soma_msu),1)))
    resto = regens - sum(rpa)
    if resto > 0: #quando a divisao dos regeneradores pelos nos nao eh exata, o excedente eh distribuido aleatoriamente
	 for  r in xrange(0, resto):
            rand = randint(0, num_nos-1)
            rpa[rand] = rpa[rand] + 1       
    if resto < 0: #quando a divisao dos regeneradores pelos nos nao eh exata e o numero de regeneradores distribuidos eh maior que o total de regeneradores existentes, a quantidade distribuida em excesso eh retirada aleatoriamente
	 for  r in xrange(0, abs(resto)):  
            rand = randint(0, num_nos-1)
	    if rpa[rand] == 0:
		rand = rpa.index(max(rpa))
	    rpa[rand] = rpa[rand] - 1
    #zera todoas as variaveis da rede para que possa ser realizada a alocacao
    req_block = 0 
    banda_block = 0
    banda_total = 0
    hops_total = 0
    primeiro_block = 0
    warmup_req = 0
    req_processadas = []
    ocupacao_rede = []
    ocupacao_links = []
    k = [0,0,0,0,0,0,0,0,0,0]
    todos_caminhos_links = []
    indice_fragmentacao = []
    bloq_parcial = []
    for r in xrange(0, num_nos):
        bloq_no_origem[r] = 0
        max_regens_usados[r] = 0
        aux_max_regens_usados[r] = 0
    for sl in xrange(0, len(slots_link)):
        for s in xrange(0, slots):
            slots_link[sl][s] = 0
    for i in xrange(0, len(fragmentacao_cada_caminho)):
	fragmentacao_cada_caminho[i] = 0.0
     
def placement_od(time, id_req, origem, destino, banda):
    global req_block 
    global banda_block
    global banda_total
    global hops_total 
    global estoque_regens
    global estoque_nao_usado
    global bloq_no_origem
    global ocupacao_rede
    global k
    global primeiro_block
    global warmup_time
    global warmup_req
    if origem == -1: #identifica que uma requisicao acabou
        if req_processadas[id_req-1] != 0: #confirma se a requisicao que acabou havia sido antendida
            fim_req = encerra_req(req_processadas[id_req-1]) #retira da rede a requisicao que acabou
            req_processadas[id_req-1] = fim_req  
    else:
        menor_custo = 999999 #variavel de comparacao que vai manter o menor custo identificado
        solucao = [[], -1, []]  #solucao = [caminho, pos_regen, recursos por segmento]
        termos = []
        status = -1
        cam_possiveis = identifica_caminho(cam, origem, destino)  #recebe todos os caminhos entre a origem e o destino, respeitando a polica de caminhos 
        for c in cam_possiveis:
            nos_itermediarios = len(c) - 2 #identifica os nos onde poderao ser usados regeneradores
            for pos_regen in xrange(2**nos_itermediarios): #calcula todas as combinacoes de posicionamento de regeneradores
                regen_map = pos_regen #posicoes codificadas em binario. Exemplo, 3 = [0,1,1] identifica dois nos do caminho 
                id_origem = 0
                id_destino = len(c)-1
                ha_espectro = True
                recursos = []  #guarda a lista de recursos desta solucao
                rotations = 0
                cf = 0  # carry flag
                while (regen_map + cf) != 0: #gera todas as combinacoes de binarios
                    cf, regen_map = regen_map & 1, regen_map >> 1  # rotate com carry
                    rotations += 1
                    if cf == 1: #identifica se a posicao do vetor correponde a 1
                        links_seg, slot_nec = quantidade_slots_nec(c, id_origem, id_origem+rotations, banda) #salva as informacoes do segmento
                        inicio, fim = aloca_espectro(sa,links_seg, slot_nec) #verifica se ha slots disponiveis para atender a requisicao no segmento
                        if inicio == -1: #identifica que nao ha slots disponiveis no segmento
                            ha_espectro = False
                            break #interrompe o calculo da combinacao
                        recursos.append([links_seg, (inicio, fim)])  #salva as informacoes ([[id_links], (slots inicial e final)]) da alocacao do segmento
                        id_origem = id_origem + rotations
                        rotations = 0
                if ha_espectro: #processa o ultimo segmento
                    links_seg, slot_nec = quantidade_slots_nec(c, id_origem, id_destino, banda) #salva as informacoes do segmento
                    inicio, fim = aloca_espectro(sa,links_seg, slot_nec) #verifica se ha slots disponiveis para atender a requisicao no segmento
                    if inicio >= 0:  #verifica se o ultimo segmento eh viavel
                        recursos.append([links_seg, (inicio, fim)])  #salva as informacoes ([[id_links], (slots inicial e final)]) da alocacao do segmento
                        sol_caminho = [c, pos_regen, recursos] #salva as informacoes da criacao do circuito todo para a combinacao
                        custo_caminho, termos_caminho = custo_od(sol_caminho) #calcula o custo da combinacao
                        if custo_caminho != 999999: #verifica se a combinacao eh viavel
                            if (custo_caminho < menor_custo): #verifica se o custo da combinacao eh o menor custo calculado ate o momento
				    #salva as informacoes da melhor solucao encontrada ate o momento
                                solucao = sol_caminho 
                                menor_custo = custo_caminho
                                termos = termos_caminho[:]
                                aux_k = cam_possiveis.index(c)
        if menor_custo < 999999: #verifica se ha solucao viavel depois de testadas todas as combinacoes em todos os k caminhos
            no_regen = identifica_no(solucao[0], solucao[1]) #identifica os nos onde serao empregados os regeneradores
            for nr in no_regen: #computa as informacoes do regeneradores
                if rpa[nr] == 0: #verifica se nao ha regenerador livre no no
                    rpa[nr] = rpa[nr]+1 #posiciona um regenerador no no
		    estoque_regens -=1 #retira um regenerador do estoque 
		    if estoque_regens < estoque_nao_usado:
                    	estoque_nao_usado = estoque_regens
            espectro = solucao[2]   #[[[links do seg], (inicio, fim)], [links do seg], (inicio, fim)]]
            aloca_req(no_regen, espectro)  #atualiza as informacoes (regeneradores, links e slots) da rede
	        #atualiza as metricas
            hops_total = hops_total + len(no_regen) + 1
            if aux_k < 11:
	        k[aux_k] += 1
            status = 2
        if (status == -1): #bloqueia a requisicao quando ela nao pode ser atendida 
            req_processadas.append(0) #salva a informacao de que a requisicao foi bloqueda
        if (time > warmup_time): #checa se o computo das metricas sera realizado
            banda_total = banda_total + banda
            if warmup_req == 0:
                warmup_req = id_req
	        #atualiza as metricas
            if (status == -1):
                req_block += 1
                banda_block = banda_block + banda
                bloq_no_origem[origem] = bloq_no_origem[origem] + 1
	        if primeiro_block == 0:
		    primeiro_block = id_req
         
#bloco: estrategias de assignmet (alocam as requisicoes nos regeneradores que estao posicionados na rede)
def executa_assignment(ra): #identifica a politica de alocacao e chama a execucao da mesma
    if ra == 'fns': 
        cont_reqs = 0 
        for r in xrange(len(req_entrantes)): #chama a execucao do FNS para cada requisicao
            if cont_reqs == reqs:
                break #para o processamento quando a ultima requisicao entrante for processada 
            fns(req_entrantes[r][0], req_entrantes[r][1], req_entrantes[r][2], req_entrantes[r][3], req_entrantes[r][4])
            cont_reqs = req_entrantes[r][1] #contabiliza as requisicoes entrantes
    if ra == 'flr': 
        cont_reqs = 0 
        for r in xrange(len(req_entrantes)): #chama a execucao do FLR para cada requisicao
            if cont_reqs == reqs:
                break #para o processamento quando a ultima requisicao entrante for processada
            flr(req_entrantes[r][0], req_entrantes[r][1], req_entrantes[r][2], req_entrantes[r][3], req_entrantes[r][4])
            cont_reqs = req_entrantes[r][1] #contabiliza as requisicoes entrantes

def fns(time, id_req, origem, destino, banda): #first narrowest spectrum - aloca usando a menor quantidade de slots possivel
    global req_block 
    global banda_block
    global banda_total
    global hops_total
    global bloq_no_origem
    global ocupacao_rede
    global k
    global primeiro_block
    global warmup_time
    global warmup_req
    if origem == -1: #identifica que uma requisicao acabou
        if req_processadas[id_req-1] != 0: #confirma se a requisicao que acabou havia sido antendida
            for nr in req_processadas[id_req-1][0]: #atualiza a informacao de uso dos regeneradores 
                aux_max_regens_usados[nr] -= 1
            fim_req = encerra_req(req_processadas[id_req-1]) #retira da rede a requisicao que acabou
            req_processadas[id_req-1] = fim_req 
    else:
        if (time > warmup_time): #checa se o computo das metricas sera realizado
            banda_total = banda_total + banda
        cam_possiveis = identifica_caminho(cam, origem, destino) #recebe todos os caminhos entre a origem e o destino, respeitando a polica de caminhos
        for c in cam_possiveis: #processa a alocacao caminho por caminho
            block = False #assume que a requisicao sera atendida
	    segmento = False #assume que nao sera necessario regenerador para atender a requisicao
            aux_k = cam_possiveis.index(c)
            no_regen = []
            espectro = []
            id_origem = 0
            id_destino = 1
	    distancia = info_links[c[id_origem], c[id_destino]][1] #recebe a distancia entre origem e destino
	    alcance_mod = modulacao[len(modulacao)-1][2] #recebe o alcance que permite a maior transmissao de banda
	    while id_destino > id_origem: #monta o segmento acrescentando um link de cada vez e comparando com o alcance da modulacao
		if id_destino == len(c) - 1: #verifica se o processamento chegou no no destino do caminho
                    segmento = True #identifica o ultimo segmento do caminho, ou caminho de um unico link
		else: 
		    no = c[id_destino]
		    while rpa[no] == 0: #considera como no destino do segmento apenas os que tenham regeneradores disponiveis para alocacao
		       id_destino += 1
		       distancia += info_links[c[id_destino-1], c[id_destino]][1] #calcula a distancia do segmento
		       no = c[id_destino]
		       if id_destino == len(c)-1: #verifica se o processamento chegou no no destino do caminho
		          segmento = True #idedntifica o ultimo segmento do caminho
			  break #para o processamento quando chega no no destino do caminho
		    if distancia > modulacao[0][2]: #verifica se a distancia do segmento pode ser alcancada 
			block = True #assume que a requisicao nao pode ser atendida quando a distancia nao pode ser alcancada por nenhuma modulacao
			break #para o processamento no referido caminho
		    if not segmento: #nao encotra segmento que possa ser atendido dentro do alcance da modulacao por falta de regeneradores
		    	for mod in xrange(len(modulacao)): #altera a modulacao para uma que permita maior alcance
        	            if distancia <= modulacao[mod][2]:
			        alcance_mod = modulacao[mod][2]
		    	aux_distancia = distancia
		    	aux_id_destino = id_destino
		   	while aux_distancia <= alcance_mod: #tenta aumentar o segmento ao maximo, respeitando o alcance da nova modulacao
			    no = c[aux_id_destino]
		            if rpa[no] != 0: #aumenta o segmento quando ha regenerador disponivel
			    	id_destino = aux_id_destino
			    	distancia = aux_distancia
		            else:
			    	no = c[id_destino] #nao aumenta o segmento
			    aux_id_destino += 1
                            aux_distancia += info_links[c[aux_id_destino-1], c[aux_id_destino]][1]
			    if aux_id_destino == len(c)-1: #verifica se o processamento chegou no no destino do caminho
			        if aux_distancia > alcance_mod: #identifica que o ultimo segmento do caminho nao pode ser alcancado pela modulacao atual
			       	    break
			    	else: #identifica que o ultimo segmento do caminho pode ser alcancado pela modulacao atual
			       	    id_destino = aux_id_destino
			            distancia = aux_distancia
				    break
		if distancia > modulacao[0][2]: #verifica se a distancia do segmento pode ser alcancada 
                    block = True #assume que a requisicao nao pode ser atendida quando a distancia nao pode ser alcancada por nenhuma modulacao
                    break
                links_seg, slot_nec = quantidade_slots_nec(c, id_origem, id_destino, banda) #salva as informacoes do segmento
                inicio_fim = aloca_espectro(sa,links_seg, slot_nec) #verifica se ha slots disponiveis para atender a requisicao no segmento
                if inicio_fim[0] == -1: #identifica que nao ha slots disponiveis no segmento
                    if id_destino == len(c)-1: #verifica se o processamento chegou no no destino do caminho
                        block = True #assume que a requisicao nao pode ser atendida quando nao ha slots suficientes
                        break
                    else: #tenta aumentar o segmento
                        id_destino += 1
                        distancia += info_links[c[id_destino-1], c[id_destino]][1]
                else: #identifica que ha slots disponiveis no segmento
                    if id_destino != len(c)-1: #inicia a montagem do proximo segmento quando o no destino do caminho nao foi atingido
                        no_regen.append(no)
                        id_origem = id_destino
                        id_destino +=1
                        distancia = info_links[c[id_origem], c[id_destino]][1]
                    else:
                        id_origem = id_destino
                    espectro.append([links_seg, inicio_fim]) #salva as informacoes ([[id_links], (slots inicial e final)]) da alocacao do segmento
            if not block: 
                break #interrompe a busca nos demais caminhos quando a requisicao pode ser atendida
        if block: #bloqueia a requisicao quando ela nao pode ser atendida em nenhum caminho
            req_processadas.append(0) #salva a informacao de que a requisicao foi bloqueda
            if (time > warmup_time): #checa se o computo das metricas sera realizado 
                if warmup_req == 0:
                    warmup_req = id_req
                req_block += 1
                banda_block = banda_block + banda
                bloq_no_origem[origem] = bloq_no_origem[origem] + 1
	        if primeiro_block == 0:
		    primeiro_block = id_req
        else: #aloca a reqisicao quando ela pode ser atendida
            for nr in no_regen: #computa as informacoes do regeneradores
                aux_max_regens_usados[nr] = aux_max_regens_usados[nr]+1 
                if aux_max_regens_usados[nr] > max_regens_usados[nr]:
                    max_regens_usados[nr] = max_regens_usados[nr]+1
            aloca_req(no_regen, espectro) #atualiza as informacoes (regeneradores, links e slots) da rede
	    #atualiza as metricas
            hops_total = hops_total + len(no_regen) + 1 
            if aux_k < 11:
	        k[aux_k] += 1
        

def flr(time, id_req, origem, destino, banda): #first longest reach - aloca usando o maior alcance possivel
    global req_block 
    global banda_block
    global banda_total
    global hops_total 
    global bloq_no_origem
    global ocupacao_rede
    global k
    global primeiro_block
    global warmup_time
    global warmup_req
    if origem == -1: #identifica que uma requisicao acabou
        if req_processadas[id_req-1] != 0: #confirma se a requisicao que acabou havia sido antendida
            for nr in req_processadas[id_req-1][0]: #atualiza a informacao de uso dos regeneradores
                aux_max_regens_usados[nr] -= 1
            fim_req = encerra_req(req_processadas[id_req-1]) #retira da rede a requisicao que acabou
            req_processadas[id_req-1] = fim_req 
    else:
        if (time > warmup_time): #checa se o computo das metricas sera realizado
            banda_total = banda_total + banda
        cam_possiveis = identifica_caminho(cam, origem, destino) #recebe todos os caminhos entre a origem e o destino, respeitando a polica de caminhos
        alcance_mod = modulacao[0][2] #identifica a modulacao de maior alcance
        for c in cam_possiveis:  #processa a alocacao caminho por caminho
            block = False #assume que a requisicao sera atendida
            aux_k = cam_possiveis.index(c)
            no_regen = []
            espectro = []
            id_origem = 0
            id_destino = len(c)-1
            distancia = 0
            while id_destino > id_origem: #monta cada segmento do caminho
                for d in xrange(id_origem, id_destino):#monta o segmento acrescentando um link de cada vez
                    distancia += info_links[c[d], c[d+1]][1] #identifica o comprimento do segmento
                while distancia > alcance_mod: #compara o comprimento do segmento com o alcance da modulacao
                    distancia -= info_links[c[id_destino-1], c[id_destino]][1] #altera o nivel de modulacao
                    id_destino -= 1
                no = c[id_destino]
                if rpa[no] != 0 or id_destino == len(c)-1: #verifica se ha regenerador ou se esta no no destino
                    links_seg, slot_nec = quantidade_slots_nec(c, id_origem, id_destino, banda) #salva as informacoes do segmento
		    inicio_fim = aloca_espectro(sa,links_seg, slot_nec) #verifica se ha slots disponiveis para atender a requisicao no segmento
                    if inicio_fim[0] == -1: #identifica que nao ha slots disponiveis no segmento
                        id_destino -= 1 #reduz o segmento em um link
                        distancia = 0
                        if id_destino == id_origem:#identifica que o segmento nao pode ser reduzido
                            block = True #assume que a requisicao nao pode ser atendida quando nao ha slots suficientes
                    else: #identifica que ha slots disponiveis no segmento
                        if id_destino != len(c)-1: #verificia se nao chegou ao no destino
                            no_regen.append(no) #salva as informacoes de alocacao do regenerador
                        espectro.append([links_seg, inicio_fim]) #salva as informacoes ([[id_links], (slots inicial e final)]) da alocacao do segmento
                        id_origem = id_destino
                        id_destino = len(c)-1
                        distancia = 0
                else: #identifica que nao esta no destino e nao ha regenerador no no
                    id_destino -= 1 #reduz o segmento em um link
                    distancia = 0
                    if id_destino == id_origem: #identifica que o segmento nao pode ser reduzido
                        block = True #assume que a requisicao nao pode ser atendida quando nao ha regenerador no no
            if not block: 
                break  #interrompe a busca nos demais caminhos quando a requisicao pode ser atendida
        if block: #bloqueia a requisicao quando ela nao pode ser atendida em nenhum caminho
            req_processadas.append(0) #salva a informacao de que a requisicao foi bloqueda
            if (time > warmup_time): #checa se o computo das metricas sera realizado 
                if warmup_req == 0:
                    warmup_req = id_req
                req_block += 1
                banda_block = banda_block + banda
                bloq_no_origem[origem] = bloq_no_origem[origem] + 1
	        if primeiro_block == 0:
		    primeiro_block = id_req
        else:  #aloca a reqisicao quando ela pode ser atendida
            for nr in no_regen: #computa as informacoes do regeneradores
                aux_max_regens_usados[nr] = aux_max_regens_usados[nr]+1
                if aux_max_regens_usados[nr] > max_regens_usados[nr]:
                    max_regens_usados[nr] = max_regens_usados[nr]+1
	    aloca_req(no_regen, espectro) #atualiza as informacoes (regeneradores, links e slots) da rede
	    #atualiza as metricas
            hops_total = hops_total + len(no_regen) + 1
            if aux_k < 11:
	        k[aux_k] += 1
              
#bloco: politica de alocacao de espectro
def aloca_espectro(sa,links_seg, slot_nec): #identifica a politica de alocacao de espectro e chama a execucao da mesma
    if sa == 'ff':
	inicio, fim = first_fit(links_seg, slot_nec)
    if sa == 'lf':
	inicio, fim = last_fit(links_seg, slot_nec)
    if sa == 'flf':
	inicio, fim = first_last_fit(links_seg, slot_nec)
    if sa == 'eff':
	inicio, fim = exact_first_fit(links_seg, slot_nec)
    return (inicio, fim)

def first_fit(links_seg, qtd_slot_nec):
    slots_seg = [] #cria uma lista de vetores
    for l in links_seg: 
        slots_seg.append(slots_link[l]) #insere na lista os vetores que correspondem aos slots de cada um dos links do seg
    ff = np.array(slots_seg, dtype = np.int) #monta uma matriz em que cada linha correponde aos slots de um link
    cont = 0
    inicio = 0
    fim = 0
    aux = np.sum(ff, axis=0) #cria um vetor auxiliar com a soma das colunas (soma=0 representa continuidade no segmento)
    ha_espectro = False
    for s in xrange(len(aux)): #le o vetor do inicio para o final
        if aux[s] == 0: #verifica a contiguidade dos slots que sao continuos
            cont +=1
            if cont == qtd_slot_nec: #verifica se ha slots contiguos e continuos em quantidade suficiente 
                inicio = s - cont + 1 #armazena o primeiro slot onde sera feita a alocacao
                fim = inicio + cont -1 #armazena o ultimo slot onde sera feita a alocacao
                ha_espectro = True #identifica que eh possivel fazer a alocacao
                break          
        else:  #identifica que os slots nao sao continuos 
            cont = 0
    if ha_espectro == False: #verifica se eh possivel fazer a alocacao ou nao
        inicio = -1
        fim = -1
    return (inicio, fim) #retorna os slots onde sera feita a alocacao, ou (-1, -1) caso a alocacao nao seja possivel

def last_fit(links_seg, qtd_slot_nec):
    slots_seg = [] #cria uma lista de vetores
    for l in links_seg:
        slots_seg.append(slots_link[l])  #insere na lista os vetores que correspondem aos slots de cada um dos links do seg
    lf = np.array(slots_seg, dtype = np.int) #monta uma matriz em que cada linha correponde aos slots de um link
    cont = 0
    inicio = 0
    fim = 0
    aux = np.sum(lf, axis=0) #cria um vetor auxiliar com a soma das colunas (soma=0 representa continuidade no segmento)
    ha_espectro = False
    for s in xrange(len(aux)-1, -1, -1): #le o vetor do fim para o inicio
        if aux[s] == 0: #verifica a contiguidade dos slots que sao continuos
            cont +=1
            if cont == qtd_slot_nec: #verifica se ha slots contiguos e continuos em quantidade suficiente
                inicio = s #armazena o primeiro slot onde sera feita a alocacao
                fim = inicio + cont -1 #armazena o ultimo slot onde sera feita a alocacao
		ha_espectro = True #identifica que eh possivel fazer a alocacao
                break         
        else: #identifica que os slots nao sao continuos
            cont = 0
    if ha_espectro == False: #verifica se eh possivel fazer a alocacao ou nao
        inicio = -1
        fim = -1
    return (inicio, fim)  #retorna os slots onde sera feita a alocacao, ou (-1, -1) caso a alocacao nao seja possivel

def exact_fit(links_seg, qtd_slot_nec):
    slots_seg = [] #cria uma lista de vetores
    for l in links_seg:
        slots_seg.append(slots_link[l]) #insere na lista os vetores que correspondem aos slots de cada um dos links do seg
    ef = np.array(slots_seg, dtype = np.int) #monta uma matriz em que cada linha correponde aos slots de um link
    cont = 0
    inicio = 0
    fim = 0
    aux = np.sum(ef, axis=0) #cria um vetor auxiliar com a soma das colunas (soma=0 representa continuidade no segmento)
    ha_espectro = False
    for s in xrange(len(aux)): #le o vetor do inicio para o final
        if aux[s] == 0: #verifica a contiguidade dos slots que sao continuos
            cont +=1
	    if s == len(aux) - 1 and cont == qtd_slot_nec: #verifica se ha slots contiguos e continuos em quantidade exata no fim do vetor
                inicio = s - cont + 1 #armazena o primeiro slot onde sera feita a alocacao
                fim = inicio + cont -1 #armazena o ultimo slot onde sera feita a alocacao
		ha_espectro = True #identifica que eh possivel fazer a alocacao exata
	else: #identifica que os slots nao sao continuos
	    if cont == qtd_slot_nec: #verifica se o ultimo bloco de slots continuos e contiguos identificados tem a quantidade exata de slots
                inicio = s - cont #armazena o primeiro slot onde sera feita a alocacao
                fim = inicio + cont -1  #armazena o ultimo slot onde sera feita a alocacao
		ha_espectro = True #identifica que eh possivel fazer a alocacao exata
		break             
	    cont = 0
    if ha_espectro == False: #verifica se eh possivel fazer a alocacao ou nao
	inicio, fim = -1, -1
    return (inicio, fim) #retorna os slots onde sera feita a alocacao, ou (-1, -1) caso a alocacao nao seja possivel

def first_last_fit(links_seg, qtd_slot_nec):
    if qtd_slot_nec < div_espectro: #verifica se a alocacao sera fist ou last fit
	inicio, fim = first_fit(links_seg, qtd_slot_nec) #chama a alocacao first-fit
    else:
	inicio, fim = last_fit(links_seg, qtd_slot_nec) #chama a alocacao last-fit
    return (inicio, fim) #retorna os slots onde sera feita a alocacao, ou (-1, -1) caso a alocacao nao seja possivel 

def exact_first_fit(links_seg, qtd_slot_nec):
    inicio, fim = exact_fit(links_seg, qtd_slot_nec) #chama a alocacao exact-fit
    if inicio == -1: #verifica se eh possivel fazer a alocacao exata
	inicio, fim = first_fit(links_seg, qtd_slot_nec) #chama a alocacao first-fit se nao for possivel a alocacao exata
    return (inicio, fim) #retorna os slots onde sera feita a alocacao, ou (-1, -1) caso a alocacao nao seja possivel 
			  
#bloco: politica de escolha de caminhos 
def k_menores_caminhos(k, origem, destino): #seleciona os k menores caminhos entre uma origem e um destino
    caminhos =[]
    aux = sorted(list(nx.all_simple_paths(G, origem, destino, cutoff=None)), key=distancia_total) #calcula e ordena por soma das distancias crescente todos os caminhos entre a origem e o destino
    if k < len(aux):
        for i in xrange(0, k): #seleciona os k primeiros caminhos da lista
            caminhos.append(aux[i])    
    else:
        caminhos = aux
    return caminhos

def delta_saltos(delta, origem, destino): #seleciona os caminhos que tenham delta saltos a mais que o numero de saltos do menor caminho entre origem e destino
    caminhos =[]
    aux = sorted(list(nx.all_simple_paths(G, origem, destino, cutoff=None)), key=len) #calcula e ordena numero de saltos crescente todos os caminhos entre a origem e o destino
    for c in range(0, len(aux)): #seleciona os caminhos que tenham delta saltos a mais que o primeiro caminho da lista
        if len(aux[c]) <= len(aux[0])+delta:
            caminhos.append(aux[c])
        else:
            break
    caminhos = sorted((caminhos), key = distancia_total) #ordena os caminhos por distancia crescente
    return caminhos

def identifica_caminho(cam, origem, destino): #identifica o metodo de calculo de caminhos que sera utilizado e separa os valores de k ou delta conforme o caso
    for ch in cam:
        if ch.isdigit():
            num = int(ch) #identifica o valor do k ou do delta
        else:
            letra = lower(ch) #identifica se o metodo eh k ou delta 
    #chama o metodo  
    if letra == 'k':
        caminhos = k_menores_caminhos(num, origem, destino)
    if letra == 'd':
        caminhos = delta_saltos(num, origem, destino)
    return caminhos


#bloco: calculos auxiliares (metodos que executam calculos que sao usados varias vezes e/ou por mais de um processo distinto)
def distancia_total(cam): #dado um caminho, retorna a distancia total dele
    total = 0
    for i in xrange(len(cam) - 1): #soma a distancia de cada link do caminho
        total += G.get_edge_data(cam[i], cam[i+1])['weight'] 
    return total

def quantidade_slots_nec(caminho, id_origem, id_destino, banda): #calcula a quantidade de slots necessarios para alocar uma requisicao, baseado no valor da banda, na distancia e nos valores de modulacao
    links_seg = []
    distancia = 0
    slots_nec = -1
    for i in xrange(id_origem, id_destino): #identifica os links do segmento e a sua distancia total
        links_seg.append(info_links[caminho[i],caminho[i+1]][0])
        distancia += info_links[caminho[i],caminho[i+1]][1]
    for m in xrange(len(modulacao)): #encontra a melhor modulacao para atender a banda requisitada 
        if distancia <= modulacao[m][2]:
            if banda % modulacao[m][1] == 0:
                slots_nec = banda/modulacao[m][1] #calcula o numero de slots necessarios quando a banda pode ser alocada exatamente
            else:
                slots_nec = trunc(banda/modulacao[m][1])+1 #calcula o numero de slots necessario quando a banda nao vai ocupar todo o espaco de todos os slots
    return links_seg, slots_nec

def custo_od(sol_caminho):
    c = sol_caminho[0] #vetor com os nos do caminho
    regen_map = sol_caminho[1] #posicoes codificadas em binario. Exemplo, 3 = [0,1,1] identifica dois nos do caminho 
    recursos = sol_caminho[2][:] #vetor com as informacoes: [[[links do seg], (inicio, fim)], [links do seg], (inicio, fim)]]
    termo_slots, termo_regen, termo_caminho, termo_usabilidade = -1, -1, -1, -1 #recebem os valores usados para o calculo do custo
    custo = 0 #recebe o custo calculado
      #variavei locais de processamento
    reg_livre = 0
    reg_disponivel = 0
    id_no = 0
    id_seg = 0
    link_mais_usado = 0
    cf = 0  # carry flag
    lista_links = []
    maior_bloco = 0
    cont = 0
    for i in xrange(0, len(recursos)):#le os segmentos
	for j in xrange(0, len(recursos[i][0])): #le o vetor de links dentro de cada segmento
            l = recursos[i][0][j]
	    lista_links.append(slots_link[l]) #instancia uma lista com os vetores que correspondem aos slots de cada um dos links do seg
    ind_f = np.array(lista_links, dtype = np.int) #monta uma matriz em que cada linha correponde aos slots de um link
    aux = np.sum(ind_f, axis=0) #cria um vetor auxiliar com a soma das colunas (soma=0 representa continuidade no segmento)
    for s in xrange(0,len(aux)): #le o vetor do inicio para o final
        if aux[s] == 0: #verifica a contiguidade dos slots que sao continuos
            cont +=1
            if s == len(aux)-1 and cont > maior_bloco:  #verifica se a quantidade de slots contiguos e continuos no fim do vetor representa o maior bloco de alocacao
                maior_bloco = cont 
        else:  #identifica que os slots nao sao continuos
            if cont > maior_bloco: #verifica se a quantidade de slots contiguos e continuos identificados representa o maior bloco de alocacao
		maior_bloco = cont 
            cont = 0
    phi = (float(maior_bloco)) / (slots) #calcula fragmentacao do caminho
    while (regen_map + cf) != 0: #gera todas as combinacoes de binarios
        slots_usados = (recursos[id_seg][1][1]-recursos[id_seg][1][0] + 1) + sum(slots_link[info_links[c[id_no], c[id_no+1]][0]]) #calcula a soma dos slots necessarios para a alocacao com os slots ja alocados em cada link
        if slots_usados > link_mais_usado: #compara a ocupacao de cada link
            link_mais_usado = slots_usados #guarda o valor do link mais ocupado
        id_no += 1
        cf, regen_map = regen_map & 1, regen_map >> 1  # rotate com carry
        if cf == 1: #identifica se a posicao do vetor correponde a 1
            if rpa[c[id_no]] > 0: #identifica o no e verifica se existe regenerador livre para alocacao
                reg_livre += 1
            else: #considera a retirada de um regenerador do estoque quando nao ha regenerador livre
                reg_disponivel += 1 
            id_seg += 1
    if reg_disponivel > estoque_regens: # verifica se ha regen suficiente no estoque para atender esta solucao
        custo = 999999 #identifica que a combinacao nao pode ser atendida por falta de regenerador
    else: #quando a combinacao pode ser atendida 
        while c[id_no] != c[-1]: #calcula a ocupacao dos slots no ultimo segmento
            slots_usados = (recursos[id_seg][1][1]-recursos[id_seg][1][0] + 1) + sum(slots_link[info_links[c[id_no], c[id_no+1]][0]])
	    if slots_usados > link_mais_usado:
                link_mais_usado = slots_usados #guarda o valor do link mais ocupado do caminho, considerando os links do ultimo segmento
            id_no += 1
	  #calcula as parcelas da equacao de custo
        termo_slots = float(link_mais_usado)/slots 
        t_regen = float((reg_disponivel + reg_livre)*regens + reg_disponivel)/max(regens*(regens+1),1)
	peso_regen = 1-float(estoque_regens - reg_disponivel)/max(regens,1)
	termo_regen = t_regen*peso_regen
	termo_caminho = float(len(c)-1)/G.number_of_edges()
	termo_usabilidade = 1- phi
        custo = c1*termo_slots + c2*termo_regen + c3*termo_caminho + c4*termo_usabilidade #calcua o custo da combinacao
    return custo, [termo_slots, termo_regen, termo_caminho, termo_usabilidade]   

def identifica_no(caminho, pos_regen): #identifica os nos da rede a partir de um caminho e um codigo binario para representacao desses nos
    cam = caminho
    print cam
    rp = [] #vetor onde serao inseridos os nos identificados
    id_no = 0
    id_seg  = 0
    cf = 0  # carry flag
    regen_map = pos_regen #posicoes codificadas em binario. Exemplo, 3 = [0,1,1] identifica dois nos do caminho  
    while (regen_map + cf) != 0: #gera todas as combinacoes de binarios
        id_no += 1
        cf, regen_map = regen_map & 1, regen_map >> 1  # rotate com carry
        if cf == 1: #identifica se a posicao do vetor correponde a 1
            rp.append(cam[id_no]) #identifica o no e insere no vetor 
        id_seg += 1
    return rp #retorna o vetor com os nos identificados

#bloco: trafego dinamico
def identifica_arq_req(topologia, amostra_req, min_bw, max_bw, reqs, taxa, dur, traf): #monta o endereco do arquivo que contem as requisicoes, baseado nos parametros de entrada
    arq_req = (url+'EON_Placement/Requisicoes/'+topologia+'_'+str(amostra_req)+'_'+str(min_bw)+'_'+str(max_bw)+'_'+str(reqs)+'_'+str(taxa)+'_'+str(dur)+'_'+traf+'.csv')
    return arq_req    
 
def carrega_req_entrantes(arq_req): #carrega as informacoes do arquivo de requisicoes para a memoria
    with open(arq_req, 'rb') as requisicao:
        reader = csv.reader(requisicao) #le o arquivo de requisicoes linha por linha
        try: 
            for linha in reader: #grava cada linha do arquivo em uma posicao do vetor req_entrantes
                req_entrantes.append((int(linha[0]), int(linha[1]), int(linha[2]), int(linha[3]), int(linha[4])))
        except csv.Error as e:
            sys.exit('Requisicao %s, linha %d: %s' % requisicao, reader.line_num, e)

def aloca_req(no_regen, espectro): #atualiza o estado da rede, alocando nos devidos slots uma requisicao que foi atendida
    global links_frag
    regen_req = no_regen
    links_req = espectro
    for r in regen_req: #atualiza as informacoes dos regeneradores que foram usados para atender a requisicao
        rpa[r] = rpa[r]-1
    for lr in xrange(0, len(links_req)): #identifica os links que serao usados para atender a requisicao
        for l in links_req[lr][0]:
            links_frag.append(l)
            for s in range(links_req[lr][1][0], links_req[lr][1][1]+1): #atualiza as informacoes dos slots do link que serao usados para atender a requisicao
                slots_link[l][s] = 1 #slots com valor 1 representam slots que estao sendo usados por uma requisicao
    req_processadas.append((no_regen, espectro)) #atualiza as informacoes da rede
    
def encerra_req(req_ativa): #atualiza o estado da rede, retirando uma requisicao que encerrou
    global links_frag
    global estoque_regens
    regens_uso = req_ativa[0]
    links_uso = req_ativa[1]
    for r in regens_uso:  #atualiza as informacoes dos regeneradores que foram liberados pela requisicao encerrada
	if rp == 'od2':
	    estoque_regens = estoque_regens + 1
	else:
            rpa[r] = rpa[r]+1
    for lu in xrange(0, len(links_uso)): #identifica os links que serao liberados pela requisicao encerrada
        for l in links_uso[lu][0]:
            links_frag.append(l)
            for s in xrange(links_uso[lu][1][0], links_uso[lu][1][1]+1): #atualiza as informacoes dos slots do link que serao liberados pela requisicao encerrada
                slots_link[l][s] = 0  #slots com valor 0 representam slots que estao disponiveis para serem utilizados
    return 0 #retona zero para que esse valor seja salvo no vetor req_processadas, indicando que a requisicao nao esta ativa na rede

#bloco: saidas
def calcula_metricas(): #le os valores das variaveis de metricas ou de processamento e retorna os valores finais das metricas calculadas
    bp = float(req_block)/(reqs-warmup_req) #retorna a probabilidade de bloqueio
    bbp = float(banda_block)/banda_total #retorna a probabilidade de bloqueio de banda
    media_hops = float(hops_total)/(reqs-req_block) #retorna a media de saltos usados para atender as requisicoes	
         #retorna o valor do numero maximo de regeneradores usados simultaneamente
    if rp == 'od' or rp == 'od2': 
	regens_usados = regens - estoque_nao_usado
    else:
    	regens_usados = sum(max_regens_usados)
    return round(bp, 12), round(bbp, 12), round(media_hops, 6), regens_usados

def gera_saida(bp, bbp, media_hops, regens_usados): #grava os resultados obtidos na simulacao em um arquivo
    arq_saida = (url+'EON_Placement/Resultados/'+topologia+'_'+str(slots)+'_'+str(regens)+'_'+str(mod)+'_'+algo+'_'+sa+'_'+
                 str(cam)+'_'+str(c1)+'_'+str(c2)+'_'+str(c3)+'_'+str(c4)+'_'+
                 str(amostra_req)+'_'+str(min_bw)+'_'+str(max_bw)+'_'+str(reqs)+'_'+
                 str(taxa)+'_'+str(dur)+'_'+traf+'.csv') #monta o caminho e nome do arquivo, baseado nos parametros de entrada
    print arq_saida
    arq = open(arq_saida, 'w') #cria o arquivo
    k1, k2, k3, k4, k5, k6, k7, k8, k9, k10 = k
    if topologia == 'cost239' or topologia == 'cost239_r': #identifica a topologia, porque topologias diferentes terao arquivos com tamanhos diferentes
        n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10 = bloq_no_origem
        arq.write(topologia+','+str(slots)+','+str(regens)+','+str(mod)+','+algo+','+sa+','+
                 str(cam)+','+str(c1)+','+str(c2)+','+str(c3)+','+str(c4)+','+
                 str(amostra_req)+','+str(min_bw)+','+str(max_bw)+','+str(reqs)+','+
                 str(taxa)+','+str(dur)+','+traf+','+str(bp)+','+str(bbp)+','+
                 str(regens_usados)+','+str(media_hops)+','+str(primeiro_block)+','+
                 str(k1)+','+str(k2)+','+str(k3)+','+str(k4)+','+str(k5)+','+str(k6)+','+str(k7)+','+str(k8)+','+str(k9)+','+str(k10)+','+
                 str(n0)+','+str(n1)+','+str(n2)+','+str(n3)+','+str(n4)+','+str(n5)+','+str(n6)+','+
                 str(n7)+','+str(n8)+','+str(n9)+','+str(n10)+"\n") #grava as informacoes no arquivo
        arq.close() #fecha o arquivo
    if topologia == 'nsfnet' or topologia == 'nsfnet_r': #identifica a topologia
        n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13 = bloq_no_origem
        arq.write(topologia+','+str(slots)+','+str(regens)+','+str(mod)+','+algo+','+sa+','+
                 str(cam)+','+str(c1)+','+str(c2)+','+str(c3)+','+str(c4)+','+
                 str(amostra_req)+','+str(min_bw)+','+str(max_bw)+','+str(reqs)+','+
                 str(taxa)+','+str(dur)+','+traf+','+str(bp)+','+str(bbp)+','+
                 str(regens_usados)+','+str(media_hops)+','+str(primeiro_block)+','+
                 str(k1)+','+str(k2)+','+str(k3)+','+str(k4)+','+str(k5)+','+str(k6)+','+str(k7)+','+str(k8)+','+str(k9)+','+str(k10)+','+
                 str(n0)+','+str(n1)+','+str(n2)+','+str(n3)+','+str(n4)+','+str(n5)+','+str(n6)+','+
                 str(n7)+','+str(n8)+','+str(n9)+','+str(n10)+','+str(n11)+','+
                 str(n12)+','+str(n13)+"\n") #grava as informacoes no arquivo
        arq.close() #fecha o arquivo
    if topologia == 'top_teste': #identifica a topologia
        n0, n1, n2, n3, n4, n5 = bloq_no_origem
        arq.write(topologia+','+str(slots)+','+str(regens)+','+str(mod)+','+algo+','+sa+','+
                 str(cam)+','+str(c1)+','+str(c2)+','+str(c3)+','+str(c4)+','+
                 str(amostra_req)+','+str(min_bw)+','+str(max_bw)+','+str(reqs)+','+
                 str(taxa)+','+str(dur)+','+traf+','+str(bp)+','+str(bbp)+','+
                 str(regens_usados)+','+str(media_hops)+','+str(primeiro_block)+','+
                 str(k1)+','+str(k2)+','+str(k3)+','+str(k4)+','+str(k5)+','+str(k6)+','+
                 str(k7)+','+str(k8)+','+str(k9)+','+str(k10)+','+
                 str(n0)+','+str(n1)+','+
                 str(n2)+','+str(n3)+','+str(n4)+','+str(n5)+"\n") #grava as informacoes no arquivo
        arq.close() #fecha o arquivo
       
def imprime_saida(bp, bbp, media_hops, regens_usados): #printa na tela os resultados obtidos
    k1, k2, k3, k4, k5, k6, k7, k8, k9, k10 = k
    if topologia == 'cost239' or topologia == 'cost239_r': #identifica a topologia, porque topologias diferentes terao arquivos com tamanhos diferentes
        n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10 = bloq_no_origem
        print(topologia+','+str(slots)+','+str(regens)+','+str(mod)+','+algo+','+sa+','+
          str(cam)+','+str(c1)+','+str(c2)+','+str(c3)+','+str(c4)+','+
          str(amostra_req)+','+str(min_bw)+','+str(max_bw)+','+str(reqs)+','+
          str(taxa)+','+str(dur)+','+traf+','+str(bp)+','+str(bbp)+','+
          str(regens_usados)+','+str(media_hops)+','+str(primeiro_block)+','+str(k1)+','+
          str(k2)+','+str(k3)+','+str(k4)+','+str(k5)+','+str(k6)+','+str(k7)+','+str(k8)+','+str(k9)+','+str(k10)+','+str(n0)+','+
          str(n1)+','+str(n2)+','+str(n3)+','+str(n4)+','+str(n5)+','+str(n6)+','+str(n7)+','+
          str(n8)+','+str(n9)+','+str(n10))
    if topologia == 'nsfnet' or topologia == 'nsfnet_r': #identifica a topologia
        n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13 = bloq_no_origem    
        print(topologia+','+str(slots)+','+str(regens)+','+str(mod)+','+algo+','+sa+','+
          str(cam)+','+str(c1)+','+str(c2)+','+str(c3)+','+str(c4)+','+
          str(amostra_req)+','+str(min_bw)+','+str(max_bw)+','+str(reqs)+','+
          str(taxa)+','+str(dur)+','+traf+','+str(bp)+','+str(bbp)+','+
          str(regens_usados)+','+str(media_hops)+','+str(primeiro_block)+','+str(k1)+','+
          str(k2)+','+str(k3)+','+str(k4)+','+str(k5)+','+str(k6)+','+str(k7)+','+str(k8)+','+str(k9)+','+str(k10)+','+str(n0)+','+
          str(n1)+','+str(n2)+','+str(n3)+','+str(n4)+','+str(n5)+','+str(n6)+','+str(n7)+','+
          str(n8)+','+str(n9)+','+str(n10)+','+str(n11)+','+str(n12)+','+str(n13))
    if topologia == 'top_teste': #identifica a topologia
        n0, n1, n2, n3, n4, n5 = bloq_no_origem
        print(topologia+','+str(slots)+','+str(regens)+','+str(mod)+','+algo+','+sa+','+
          str(cam)+','+str(c1)+','+str(c2)+','+str(c3)+','+str(c4)+','+
          str(amostra_req)+','+str(min_bw)+','+str(max_bw)+','+str(reqs)+','+
          str(taxa)+','+str(dur)+','+traf+','+str(bp)+','+str(bbp)+','+
          str(regens_usados)+','+str(media_hops)+','+str(primeiro_block)+','+str(k1)+','+
          str(k2)+','+str(k3)+','+str(k4)+','+str(k5)+','+str(k6)+','+str(k7)+','+str(k8)+','+str(k9)+','+str(k10)+','+str(n0)+','+
          str(n1)+','+str(n2)+','+str(n3)+','+str(n4)+','+str(n5))

                
#MAIN 
seed(18) #define a semente usada nas escolhas aleatorias feitas pelo programa
#chama os metodos de inicializacao da rede
identifica_algoritmo(algo)
identifica_modulacao(mod)
carrega_topologia(topologia)
cria_slots(slots)
#chama os metodos para execucao do posicionamento e alocacao dos regeneradores, bem como do gera o arquivo de resultados, respeitando as especificidades de cada caso (exemplo: OD faz tudo em um processo so... MSU necessita rodar a politica de alocacao duas vezes...)
if rp == 'od' or rp == 'od2':
   carrega_variaveis_vetoriais(0)   
   arquivo = identifica_arq_req(topologia, amostra_req, min_bw, max_bw, reqs, taxa, dur, traf)
   carrega_req_entrantes(arquivo)
   print ('Executando o placement...') #printa essa informacao para mostrar que o programa esta rodando corretamente
   executa_placement(rp)
   print ('Escrevendo arquivo de saida') #printa essa informacao para mostrar que o arquivo com os resultados foi gerado
   bp, bbp, media_hops, regens_usados = calcula_metricas()
   gera_saida(bp, bbp, media_hops, regens_usados)
   imprime_saida(bp, bbp, media_hops, regens_usados)
if rp == 'up' or rp == 'nd' or rp == 'tw':
   carrega_variaveis_vetoriais(0)
   if regens != 0: #nao executa o posicionamento quando nao ha regeneradores para distribuir   
	executa_placement(rp)
   arquivo = identifica_arq_req(topologia, amostra_req, min_bw, max_bw, reqs, taxa, dur, traf)
   carrega_req_entrantes(arquivo)
   print ('Executando o assignment...')  #printa essa informacao para mostrar que o programa esta rodando corretamente
   executa_assignment(ra)
   print ('Escrevendo arquivo de saida') #printa essa informacao para mostrar que o arquivo com os resultados foi gerado
   bp, bbp, media_hops, regens_usados = calcula_metricas()
   gera_saida(bp, bbp, media_hops, regens_usados)
   imprime_saida(bp, bbp, media_hops, regens_usados)
if rp == 'msu':
   if regens == 0: #quando nao ha regeneradores para distribuir na rede carrega o rpa com 0
       carrega_variaveis_vetoriais(0)
   else:
       carrega_variaveis_vetoriais(999999) #quando ha regeneradores para distribuir na rede carrega o rpa com infinitos para permitir o calculo do posicinamento 
   arquivo = identifica_arq_req(topologia, amostra_req, min_bw, max_bw, reqs, taxa, dur, traf)
   carrega_req_entrantes(arquivo)
   if regens != 0: #nao executa o posicionamento quando nao ha regeneradores para distribuir
       executa_placement('msu')
   print ('Executando o assignmeint...')  #printa essa informacao para mostrar que o programa esta rodando corretamente
   executa_assignment(ra)
   print ('Escrevendo arquivo de saida') #printa essa informacao para mostrar que o arquivo com os resultados foi gerado
   bp, bbp, media_hops, regens_usados = calcula_metricas()
   gera_saida(bp, bbp, media_hops, regens_usados)
   imprime_saida(bp, bbp, media_hops, regens_usados) 

