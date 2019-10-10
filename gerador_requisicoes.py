import argparse
import random
import math
import numpy as np
import csv
import sys

#recebe os parametros passados
parser = argparse.ArgumentParser(description='Gera requisicoes')
parser.add_argument("-top", default='cost239_r', help = 'Nome da topologia desejada', type = str)
parser.add_argument("-amostra", default=0, help = 'Numero da amostra da requisicao que sera executada', type = int)
parser.add_argument("-min_bw", default=100, help = 'Valor minimo da banda das requisicoes', type = int)
parser.add_argument("-max_bw", default=400, help = 'Valor maximo da banda das requisicoes', type = int)
parser.add_argument("-reqs", default=200, help = 'Quantidade de requisicoes que serao executadas', type = int)
parser.add_argument("-taxa", default=1.0, help = 'Taxa de chegada das requisicoes', type = float)
parser.add_argument("-dur", default=360.0, help = 'Duracao media das requisicoes', type = float)
parser.add_argument("-traf", default='u', help = 'Tipo de padrao de trafego', type = str)

args = parser.parse_args()

#bloco: variaveis globais
    #parametros (variaveis com os valores de entrada que nao sao alterados)
topologia = args.top
amostra_req = args.amostra
min_bw = args.min_bw
max_bw = args.max_bw
reqs = args.reqs
taxa = args.taxa
dur = args.dur
traf = args.traf
url = '/home/user/' #identifica o caminho onde esta a pasta do simulador
np.random.seed(amostra_req+15) #define a semente usada nas escolhas aleatorias feitas pelo programa usando uma semente diferente em cada amostra
banda = [100, 200, 400] #valores que serao escolhidos aleatoriamente para a banda de cada requisicao

print ('Gerando arquivo com %d requisicoes de trafego tipo %s para a rede %s.' %(reqs, traf, topologia)) #printa essa informacao para mostrar que o programa esta rodando corretamente

arquivo = (url+'EON_Placement/Requisicoes/'+str(topologia)+'_'+str(amostra_req)+'_'+str(min_bw)+'_'+str(max_bw)+'_'+str(reqs)+'_'+str(taxa)+'_'+str(dur)+'_'+str(traf)+'.csv')  #monta o caminho e nome do arquivo, baseado nos parametros de entrada

if traf == 'u':#identifica o tipo de trafego (uniformemente distribuido), permitindo a insersao futura de outros tipos
	#identifica a topologia, porque topologias diferentes terao origens e destinos diferentes
    if topologia == 'cost239' or topologia == 'cost239_r':
	total_nos = 11
    if topologia == 'nsfnet' or topologia == 'nsfnet_r':
	total_nos = 14
    with open(arquivo,"w") as f:
        now=0  	#marca o inicio de uma demanda, pode ter mais de uma por momento
    	demandas=[]	#auxiliar para a ordenacao
    	for d in range(1, reqs+1):  #cria todas as requisicoes		
    	    p=np.random.poisson(taxa) #gera um numero aleatorio para o calculo do instante de chegada de cada requiaicao
	    now = now+int(p) #calcula o instante da chegada da requisicao
    	    duracao = max(int(np.random.exponential(dur)),1) #gera duracao da requisicao
	    src = np.random.randint(0, total_nos) #seleciona a origem
	    dst = np.random.randint(0, total_nos) #seleciona o destino
            while (dst == src): #garante que origem e destino sao nos diferentes
		dst = np.random.randint(0, total_nos)   
            bw = banda[np.random.randint(0, len(banda))] #seleciona a banda
	    demandas.append([now, d, src, dst, bw]) #cria uma requisicao
	    demandas.append([now+duracao, d, -1, -1, -1]) #cria o instante de encerramento da requisicao
        demandas.sort() #ordena as requisicoes e seus instantes de encerramento em ordem cronologica
        for d in demandas: #grava os resultados obtidos na simulacao em um arquivo
    	    f.write (str(d[0]).zfill(5)+","+str(d[1]).zfill(4)+","+str(d[2])+","+str(d[3])+","+str(d[4])+"\n")     
    	f.close()
