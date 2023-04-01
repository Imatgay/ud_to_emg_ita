import pyconll
import json
import argparse

lemma_info = {}
duplicate_dict = {}
triplicate_dict = {}
quadruplicate_dict = {}
quintuplicate_dict = {}
sext_dict = {}
ept_dict = {}
oct_dict = {}
nine_dict = {}

added_nine = 0

local_back_dep = 0
backward_dep = 0
dependencies = 0
sentencs = 0
orphan = 0


parser = argparse.ArgumentParser(description='Convert a CoNLL-U file to eMG lexicon. Language: it.')
parser.add_argument('-i', '--input', type=str, help='Input CoNLL-U file name', required=True)
args = parser.parse_args()
file_name = args.input

sentences = pyconll.load_from_file(file_name)

ambigous_tokens = 0

root_token = pyconll.unit.token.Token('0\troot\t_\tROOT\t_\t_\t0\t_\t_\t_', True) #creazione di un token ROOT, primo elemento di ogni token_dict, per gestire i token.head = 0
aux_verb_counter = 0
aux_aux_counter = 0
pass_subj_counter = 0
cop_det_subj = 0
cop_no_subj = 0
fixed_exp = 0
verb_adp = 0
token_processed = 0
det_det = 0
det_constr = 0
adp_selector = 0
verb_select_adp_det = 0
prep_art = 0
prep_art_case_fixed = 0
pron_rel = 0
sub_adp = 0
sub_adv = 0
sconj_cconj = 0
sconj_subj_det = 0
sconj_no_subj_det = 0
sconj_verb = 0
verb_det_obj = 0
possessivi = 0
head_0 = 0
aux_part_aux = 0
ultima_modifica = 0
added_du = 0
added_tr = 0
added_q = 0
                        
#####################################################################################à
#################################################################### Definiamo alcune funzioni

def get_subject_id(token, token_dict, original_dict):     ##funzione per risalire a id del soggetto, sulla base dei diversi tipi di verbi. Da implementare i rapporti con i verbi di tempo non finito
    subj_id = [] 
    if get_verb_type(token) == 'verb_fin':        
        for x in token_dict.values():
            if x is None:
                continue
            if get_original_head(x, original_dict) == token.id:
                if x.deprel == 'nsubj':
                    subj_id.append(x.id)
                    return subj_id
                elif x.deprel == 'expl:impers':
                    subj_id.append('0')
                    return subj_id
                elif x.deprel == 'nsubj:pass':
                    subj_id.append(token_dict[x.id].id)
                    return subj_id
                elif x.deprel == 'expl':
                    for y in token_dict.values():
                        if y.deprel == 'nsubj' and original_dict[y.id] == token.id:
                            subj_id.append(token_dict[y.id].id)
                            return subj_id
                        else:
                            continue
                        
    elif get_verb_type(token) == 'aux_copula':
        for x in token_dict.values():
            if x.deprel in ['nsubj','root'] and original_dict[x.id] == original_dict[token.id]:
                subj_id.append(token_dict[x.id].id)
                return subj_id
    elif get_verb_type(token) == 'aux_modal':
        for x in token_dict.values():
            if x.deprel in ['nsubj','root'] and original_dict[x.id] == original_head:
                subj_id.append(x.id)
                return subj_id
    elif get_verb_type(token) == 'aux_tense':
        for x in token_dict.values():
            if x.deprel in ['nsubj','root'] and original_dict[x.id] == original_dict[token.id]:
                subj_id.append(x.id)
                return subj_id
    elif get_verb_type(token) == 'aux_pass':
        for x in token_dict.values():
            if x.upos == 'VERB':
                subj_id.append(token_dict[original_dict[original_head]].id)
                return subj_id
    return None

    
def get_verb_type(token): ###funzione per determinare il tipo di verbo
    aux_copula = 'aux_copula'
    aux_tense = 'aux_tense'
    aux_modal = 'aux_modal'
    aux_pass = 'aux_pass'
    verb_inf = 'verb_inf'
    verb_ger = 'verb_ger'
    verb_part = 'verb_part'
    verb_fin = 'verb_fin'
    if token.upos not in ['AUX','VERB']:
        return ''
    if token.upos == 'AUX':
        if token.deprel == 'cop':
            return aux_copula
        elif token.deprel == 'aux':
            if token.lemma in ['essere','avere']:
                return aux_tense
            else: 
                return aux_modal           
        elif token.deprel == 'aux:pass':
            return aux_pass
    else:
        if 'VerbForm' in token.feats and 'Fin' in token.feats['VerbForm']:
            return verb_fin
        elif 'VerbForm' in token.feats and 'Inf' in token.feats['VerbForm']:
            return verb_inf
        elif 'VerbForm' in token.feats and 'Ger' in token.feats['VerbForm']:
            return verb_ger
        elif 'VerbForm' in token.feats and 'Part' in token.feats['VerbForm']:
            return verb_part
                    
def extract_feats(token):    ### funzione per estrarre le feats necessarie per popolare il campo agree dell'output
    if 'Number' in token.feats and 'Person' in token.feats:
        number = list(token.feats['Number'])[0]
        person = list(token.feats['Person'])[0]
        return f"{number[0].lower()}.{person.lower()}"
    elif 'Gender' in token.feats and 'Number' in token.feats:
        gender = list(token.feats['Gender'])[0]
        number = list(token.feats['Number'])[0]
        return f"{number[0].lower()}.{gender[0].lower()}"
    elif 'Gender' in token.feats and 'Number' not in token.feats:
        gender = list(token.feats['Gender'])[0]
        return f"{gender[0].lower()}."
    elif 'Number' in token.feats and 'Gender' not in token.feats:
        number = list(token.feats['Number'])[0]
        return f"{number[0].lower()}."
    else:
        return""

def get_children(father, token_dict):  ###funzione per individuare tutti i token che nella treebank originaria dipendono dal token corrente (father)
    children = []
    for token in token_dict.values():
        if father.id == token.head:
            children.append(token)
    return children

def get_original_head(token, original_dict):   ###funzione per individuare la head originaria (= il suo id) del token, senza accedere al token_dict (in cui le dipendenze sono sovrascritte)
    original_head = original_dict[token.id]
    return original_head

def det_construction(target, original_dict, token_dict):
    for token in token_dict.values():
        if token.upos == 'DET' and original_dict[token.id] == target.id:
            return token
    return None

        

def get_previous_token(token, token_dict):
    
    sorted_keys = sorted([int(key) for key in token_dict.keys()])
    if int(token.id) not in sorted_keys:
        return None
    index = sorted_keys.index(int(token.id))
    if index == 0:
        return None
    return token_dict[str(sorted_keys[index-1])]

def get_next_token(current_token, token_dict):
    
    sorted_keys = sorted([int(key) for key in token_dict.keys()])
    if int(token.id) not in sorted_keys:
        return None
    index = sorted_keys.index(int(token.id))
    if index == len(sorted_keys)-1:
        return None
    return token_dict[str(sorted_keys[index+1])]

###########################################################################################
###########################################################  Passiamo all'analisi delle frasi
for sentence in sentences:
    sentencs += 1
    original_dict = {'0':''}  ###dizionario che sarà popolato con coppie token.id : token.head 
    token_dict = {'0':root_token} ###dizionario che sarà popolato con coppie 'n':token (la chiave n sarà sempre uguale al token.id), su cui saranno rivalutate le dipendenze
    expect = []  ### inizializzazione dizionario utile per poi popolare il campo 'expect' dell'output
    
    for token in sentence:
        if '-' in token.id or '.' in token.id or token.upos in ['PUNCT']: ###non inserire multiwords (es. preposizioni articolate) in token_dict 
            continue
        token_dict[token.id] = token ### popoliamo il token_dict
        original_dict[token.id] = token.head ###popoliamo l'original_dict
    
    for token in token_dict.values():
        token_processed += 1
        if token.form == 'root': 
            continue
        original_head = get_original_head(token, original_dict) ### inizializziamo per ogni token la sua original_head, tranne che per il token root
        previous_token = get_previous_token(token, token_dict) #individuiamo il token precedente
        next_token = get_next_token(token, token_dict) #individuiamo il token successivo
  ########################
  ########################  APPLICAZIONE DI UNA SERIE DI REGOLE PER RIVALUTARE LE DIPENDEZE NELLA PROSPETTIVA DEL CAMPO EXPECT DELL'OUTPUT

        
        ## rapport ausiliare/VERB: AUX seleziona il proprio verbo di riferimento, non il contrario
      
        if token.upos == 'AUX' and token_dict[original_head].upos == 'VERB':  ##alternativa da aggiungere: and 'aux:pass' not in token.deprel 
            token_dict[original_head].head = token.id
            aux_verb_counter += 1
            if token_dict[original_head].deprel == 'root' :
                token_dict[token.id].head = '0'
            else:
                continue
                
            
        ##verbi composti (regola 'lineare')
        
        if token.upos == 'AUX' and next_token in token_dict.values() and next_token.upos == 'AUX':
            token_dict[next_token.id].head = token.id
            aux_aux_counter += 1
            
        ### costruzioni passive: rivalutare l'ausiliare come selezionato dal soggetto 
        if token.deprel == 'aux:pass':
            for x in token_dict.values():
                if x.deprel == 'nsubj:pass' and original_dict[x.id] == original_dict[token.id]: #se è una costruzione verbale composta (aux+aux+part), bisogna considerare il primo aux
                    if previous_token in token_dict.values() and previous_token.upos == 'AUX' and token_dict[original_head].upos == 'VERB':
                        #token_dict[previous_token.id].head = x.id
                        token_dict[token.id].head = previous_token.id
                        target = x
                        det = det_construction(target, original_dict, token_dict)
                        if det is not None:
                            token_dict[det.id].head = previous_token.id
                            pass_subj_counter += 1
                        else:
                            token_dict[x.id].head = previous_token.id
                      
                    else: #per le costruzioni passive semplici (aux + part)
                         token_dict[x.id].head = token.id

        
     

                
        
        ##costruzioni copulari
        if token.deprel == 'cop':
            target = token_dict[original_head]

            if target.upos in ['ADJ']:
                token_dict[original_head].head = token.id
                token_dict[token.id].head = 0
           
            if target.upos in ['PRON','NOUN','PROPN','ADJ']:
                det = det_construction(target, original_dict, token_dict)
                if det is not None:
                    token_dict[det.id].head = token.id

                    cop_det_subj += 1
                
            else:
                token_dict[original_head].head = token.id

                cop_no_subj += 1
            for x in token_dict.values():
                subj = False
                if x.deprel == 'nsubj' and original_dict[x.id] == original_dict[token.id]:
                    subj = True
                    complex_verb_construction= False
                    if previous_token is None:
                        token_dict[x.id].head = token.id
                    if previous_token is not None and previous_token.upos != 'AUX':
                        complex_verb_construction= True
                        target = token_dict[x.id]
                        det = det_construction(target, original_dict, token_dict)
                        if det is not None:
                            token_dict[det.id].head = token.id
                            token_dict[token.id].head = '0'
                        else:
                            token_dict[x.id].head = token.id
                            token_dict[token.id].head = '0'
                    elif previous_token is not None and previous_token.upos == 'AUX':
                        token_dict[x.id].head = previous_token.id
                        
                elif x.deprel == 'root' and original_head == x.id: ###se l'elemento post-copula è la root in UD
                    if previous_token is not None and previous_token.upos == 'AUX':
                        token_dict[previous_token.id].head = '0'
                    
        

        #costruzioni come "caso di pensare"
        if token.upos == 'VERB' and token.deprel == 'acl' and token_dict[original_head].upos == 'NOUN':
            for x in token_dict.values():
                if x.deprel == 'mark' and original_dict[x.id] == token.id:
                    token_dict[token.id].head = x.id
                    token_dict[x.id].head = original_dict[token.id]

                    fixed_exp += 1
        
        #il verbo seleziona il det o l'adp successivo ????? 
        if token.upos in ['AUX','VERB'] and next_token in token_dict.values() and next_token.upos in ['ADP']: #['DET','ADP']
            token_dict[next_token.id].head = token.id

            verb_adp += 1


        #se ci sono due det in sequenza, il primo seleziona il secondo
        if token.upos == 'DET' and next_token in token_dict.values() and next_token.upos == 'DET':
            token_dict[next_token.id].head = token.id

            det_det += 1

        #è il det a selezionare il noun,pron,propn
        if token.upos == 'DET':
            if token_dict[original_head].upos in ['PROPN','PRON','NOUN','NUM']:
                token_dict[original_head].head = token.id
                
                det_constr += 1
            elif token_dict[original_head].upos not in ['PROPN','PRON','NOUN','NUM']: ##per eventuali situazioni come simboli (numerale selezionato non direttamente da det)
                r = token_dict[original_head].head
                if token_dict[r].upos in ['PROPN','PRON','NOUN']:
                    token_dict[r].head = token.id


        #rapporto aggettivo/noun-propn-prop

        #preposizioni e nomi (se è preposizione con case e la sua original head è posizionata dopo nella frase, l'ADP la seleziona)
        if token.upos == 'ADP' and token.deprel == 'case':
            if int(original_dict[token.id]) > int(token.id):
                if original_dict[original_head] != '0':
                    token_dict[token.id].head = original_dict[original_head]
                else:
                    token_dict[token.id].head = previous_token.id
                    

                adp_selector += 1
                ########da cosa l'adp è selezionato da quello
            if next_token in token_dict.values() and next_token.upos == 'DET':
                f = original_dict[original_head]
                for x in token_dict.values():
                    if x.upos in ['VERB','AUX'] and x.id == token_dict[f].id :
                        token_dict[token.id].head = x.id

                        verb_select_adp_det += 1
                    else:
                        continue


                
        #trattamento preposizioni articolate                
        if token.upos == 'ADP' and next_token in token_dict.values() and next_token.upos == 'DET':
            token_dict[next_token.id].head = token.id
            if original_dict[original_head] != '0':
                token_dict[token.id].head = original_dict[original_head]

                prep_art += 1

            else:
                continue

        #cancellato un po' di cose
        #fare dipendere pronomi relativi da "antecedenti"
        if token.upos == 'PRON' and ('PronType' in token.feats and 'Rel' in token.feats['PronType']):
            s = original_dict[original_head]
            if s != '':
                token_dict[token.id].head = token_dict[s].id

                pron_rel += 1
            
                

                
        #gestione di introduzione di subordinate
        if token.deprel == 'mark':
            
            if token.upos == 'ADP':  ### introdotte da adp
                if get_verb_type(token_dict[original_head]) == 'verb_inf': #preposizione è head di verbo all'infinito
                    token_dict[original_head].head = token.id
                    token_dict[token.id].head = original_dict[original_head]

                    sub_adp += 1
                
            if token.upos == 'ADV':  ### introdotte da avverbi 
                if next_token in token_dict.values() and next_token.deprel == 'fixed':
                    token_dict[next_token.id].head = token.id
                    token_dict[original_head].head = token_dict[next_token.id].id ##original head è sempre il verbo della subordinata

                    sub_adv += 1
                
            if token.upos == 'SCONJ':     ### introdotte da coniugazioni subordinanti
                r = original_dict[original_head]               
                token_dict[token.id].head = token_dict[r].id
                token_dict[original_head].head = token.id
                for x in token_dict.values():
                    if x.upos == 'CCONJ' and original_dict[x.id] == original_head:
                        token_dict[token.id].head = x.id

                        sconj_cconj += 1
                        
                    prev_token = get_previous_token(x, token_dict)
                    if x.deprel == 'nsubj' and original_dict[x.id] == original_dict[token.id]:
                        for y in token_dict.values():
                            if y.upos == 'DET' and original_dict[y.id] == x.id:
                                token_dict[y.id].head = token.id

                                sconj_subj_det += 1
                            else:
                                token_dict[x.id].head = token.id
                                sconj_no_subj_det += 1
                            
                    elif x.upos in ['VERB','AUX'] and original_dict[x.id] == original_head and int(x.id) > int(token.id):
                        token_dict[x.id].head = token.id

                        sconj_verb +=1
                        
                    
                            

        if token.upos == 'CCONJ':
            f = original_dict[original_head]
            token_dict[token.id].head = f
            cat = token_dict[original_head].upos
            if f != '':
                if cat == token_dict[f].upos:
                    token_dict[original_head].head = token.id
            if next_token is not None:
                if next_token.upos in ['DET', 'ADV']:
                    token_dict[next_token.id].head = token.id

            for x in token_dict.values():
                if x.upos == 'SCONJ' and original_dict[x.id] == original_head:
                    token_dict[x.id].head = token.id
                    
    # rapporto soggeto/verbo   
        #if token.upos in ['AUX','VERB']:
         #   subj_id = get_subject_id(token,token_dict, original_dict)
          #  if subj_id is not None:
               # token_dict[token.id].head = subj_id[0]
                #if token_dict[subj_id[0]].head != None:
                 #   subj_has_head = False
                  #  for x in original_dict.values():
                   #     if x == subj_id[0]:
                    #        subj_has_head = True
                     #       break
                    #if not subj_has_head:
                     #   if token_dict[subj_id[0]].upos != 'PRON':
                      #      token_dict[subj_id[0]].head = '0'
    #rapporto verbo/oggetto introdotto da det (il verbo seleziona il det) 
        if token.deprel == 'obj':
            for x in token_dict.values():
                if x.upos == 'DET' and original_dict[x.id] == token.id:
                    token_dict[x.id].head = original_dict[token.id]

                    verb_det_obj +=1
        
                    

    #gli avverbi#eliminato

                


##pulizia finale dipendenze residue
    for token in token_dict.values():
        original_head = get_original_head(token, original_dict) 
        previous_token = get_previous_token(token, token_dict) 
        next_token = get_next_token(token, token_dict)
        
        #if token_dict[token_dict[token_dict[token.id].head].head].head == token.id:
         #   print(token.id, token.form, token.head)
          #  token_dict[token.id].head = '0'
           # print(token.id, token.form, token.head)
        if token.deprel in ['nsubj','nsubj:pass'] and token_dict[original_head].upos in ['VERB','AUX']:
            target = token
            det = det_construction(target, original_dict, token_dict)
            if det is not None:
                continue
            else:
                token_dict[token.id].head = original_head


            ultima_modifica +=1
        if token.upos == 'PRON' and ('PronType' in token.feats and 'Rel' in token.feats['PronType']) and token.deprel in ['nsubj','nsubj:pass']:
            for x in token_dict.values():
                if int(x.id) > int (token.id) and x.upos in ['AUX','VERB']:
                    subj_id = get_subject_id(x,token_dict, original_dict)
                    if subj_id is not None and subj_id[0] == token.id:
                        token_dict[x.id].head = token.id
            
        if token.upos == 'DET' and 'Poss' in token.feats and previous_token in token_dict.values() and previous_token.upos == 'DET':
            token_dict[token.id].head = original_head
            token_dict[original_head].head = previous_token.id
            possessivi += 1
        elif token.upos == 'DET' and token.head == get_original_head(token, original_dict) and token_dict[original_head].upos in ['PROPN','NOUN'] and token_dict[original_head].id > token.id:
            token_dict[token.id].head = '0'

            head_0 +=1
        elif token.upos == 'ADV' and token.deprel == 'advmod':
            if next_token in token_dict.values() and next_token.upos == 'ADV':
                token_dict[token.id].head = token_dict[next_token.id].head
                token_dict[next_token.id].head = token.id
        elif token.upos == 'AUX' and 'aux:pass' in token.deprel and 'VerbForm' in next_token.feats and 'Part' in next_token.feats['VerbForm'] and previous_token.upos == 'AUX':
            token_dict[token.id].head = previous_token.id

            aux_part_aux +=1


    
    


 ###############################################################################
 ###############################################################################
 ###############################################################################     
 ###### Dopo le rivalutazioni delle dipendenze, sovrascritte nei token che sono i value nel token_dict, estraiamo il campo expect per ogni token

    for token in sentence:
        if token.upos in ['PUNCT']:
            continue
        expect_dict = {}  #inizializziamo il dizionario per gli elementi 'expect'
        children = get_children(token, token_dict) #individuiamo i children di ogni token lavorando sul token_dict
        for child in children:
            dependencies += 1
            expect_dict[len(expect_dict)] = child.upos   ###aggiungiamo ogni children come valore nell'expect_dict, con chiave crescente da 0 a len(expect_dict)
            if token.id > child.id:
                backward_dep += 1
                if int(child.id) == int(token.id) - 1:
                    local_back_dep += 1
        if '-' not in token.id and '.' not in token.id and token.upos not in ['PUNCT']:
            if token_dict[token.id].head != int and len(children) == 0:
                orphan += 1
            #if token.form == 'il' and token.upos == 'DET' and child.upos == 'ADJ':
                
                #print(token.form, child.form)
                #print ('prev',previous_token.form)
            #else:
                #continue
        
        # inseriamo i dati estratti e rilevanti in lemma_info (lista unica inizializzata a inizio programma da cui attingeremo per produrre l'output)
        if lemma_info.get(token.form.lower()):
            #print (f'"{token.form}" is ambigous')
            if lemma_info.get(token.form.lower()).get('label')[0].get("0") != token.upos: ###stessa forma grafica ma upos diversi
                added_du += 1
                if duplicate_dict.get(token.form.lower()):
                    if duplicate_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                        if triplicate_dict.get(token.form.lower()):
                            if triplicate_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                                if quadruplicate_dict.get(token.form.lower()):
                                    if quadruplicate_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                                        if quintuplicate_dict.get(token.form.lower()):
                                            if quintuplicate_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                                                if sext_dict.get(token.form.lower()):
                                                    if sext_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                                                        if ept_dict.get(token.form.lower()):
                                                            if ept_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                                                                if oct_dict.get(token.form.lower()):
                                                                    if oct_dict.get(token.form.lower()).get('label')[0].get("0") != token.upos:
                                                                        nine_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                                                                    'expected': [{"0": token.upos}],
                                                                                                  'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                                                                    'agree': extract_feats(token),},})
                                                                        added_nine += 1
                                                                        
                                                                    else:
                                                                        for x in expect_dict.values():
                                                                            if not any (x in oct_dict[token.form.lower()]['expect'][i].values() for i in range(len(oct_dict[token.form.lower()]['expect'])) ):
                                                                                oct_dict[token.form.lower()]['expect'][0][str(len(oct_dict[token.form.lower()]['expect'][0]))] = x
                                                                            else:
                                                                                continue
                                                                        
                                                                else:
                                                                    oct_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                                                                    'expected': [{"0": token.upos}],
                                                                                                  'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                                                                    'agree': extract_feats(token),},})
                                                                                                 

                                                            else:
                                                                for x in expect_dict.values():
                                                                    if not any (x in ept_dict[token.form.lower()]['expect'][i].values() for i in range(len(ept_dict[token.form.lower()]['expect'])) ):
                                                                        ept_dict[token.form.lower()]['expect'][0][str(len(ept_dict[token.form.lower()]['expect'][0]))] = x
                                                                    else:
                                                                        continue
                                                        else: 
                                                            ept_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                                                        'expected': [{"0": token.upos}],
                                                                                       'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                                                        'agree': extract_feats(token),},})
                                        
                                                    else:
                                                        for x in expect_dict.values():
                                                            if not any (x in sext_dict[token.form.lower()]['expect'][i].values() for i in range(len(sext_dict[token.form.lower()]['expect'])) ):
                                                                sext_dict[token.form.lower()]['expect'][0][str(len(sext_dict[token.form.lower()]['expect'][0]))] = x
                                                            else:
                                                                continue
                                                else: 
                                                    sext_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                                                'expected': [{"0": token.upos}],
                                                                               'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                                                'agree': extract_feats(token),},})
                                                                                                    
                                            else:
                                                for x in expect_dict.values():
                                                    if not any (x in quintuplicate_dict[token.form.lower()]['expect'][i].values() for i in range(len(quintuplicate_dict[token.form.lower()]['expect'])) ):
                                                        quintuplicate_dict[token.form.lower()]['expect'][0][str(len(quintuplicate_dict[token.form.lower()]['expect'][0]))] = x
                                                    else:
                                                        continue
                                        else: 
                                            quintuplicate_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                                        'expected': [{"0": token.upos}],
                                                                       'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                                        'agree': extract_feats(token),},})
                                            added_tr += 1
                                    else:
                                        for x in expect_dict.values():
                                            if not any (x in quadruplicate_dict[token.form.lower()]['expect'][i].values() for i in range(len(quadruplicate_dict[token.form.lower()]['expect'])) ):
                                                quadruplicate_dict[token.form.lower()]['expect'][0][str(len(quadruplicate_dict[token.form.lower()]['expect'][0]))] = x
                                            else:
                                                continue
                                else: 
                                    quadruplicate_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                                'expected': [{"0": token.upos}],
                                                               'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                                'agree': extract_feats(token),},})
                                    added_tr += 1
                            else:
                                for x in expect_dict.values():
                                    if not any (x in triplicate_dict[token.form.lower()]['expect'][i].values() for i in range(len(triplicate_dict[token.form.lower()]['expect'])) ):
                                        triplicate_dict[token.form.lower()]['expect'][0][str(len(triplicate_dict[token.form.lower()]['expect'][0]))] = x
                                    else:
                                        continue
                        else: 
                            triplicate_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                        'expected': [{"0": token.upos}],
                                                       'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                        'agree': extract_feats(token),},})
                            added_tr += 1
                    else: ###stessa forma grafica e stesso upos
                        for x in expect_dict.values():
                            if not any (x in duplicate_dict[token.form.lower()]['expect'][i].values() for i in range(len(duplicate_dict[token.form.lower()]['expect'])) ):
                                duplicate_dict[token.form.lower()]['expect'][0][str(len(duplicate_dict[token.form.lower()]['expect'][0]))] = x
                            else:
                                continue    
                else:
                    duplicate_dict.update({token.form.lower():{'label': [{"0": token.upos}],
                                                'expected': [{"0": token.upos}],
                                               'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                                'agree': extract_feats(token),},})
                    
                #print (duplicate_dict)
            else: ###stessa forma grafica e stesso upos
                for x in expect_dict.values():
                    if not any (x in lemma_info[token.form.lower()]['expect'][i].values() for i in range(len(lemma_info[token.form.lower()]['expect'])) ):
                        lemma_info[token.form.lower()]['expect'][0][str(len(lemma_info[token.form.lower()]['expect'][0]))] = x
                    else:
                        continue
        else:
            lemma_info.update({token.form.lower():{'label': [{"0": token.upos}],
                                           'expected': [{"0": token.upos}],
                                           'expect': [{str(i): expect_dict[i] for i in range(len(expect_dict))}] if expect_dict else [{}],
                                            'agree': extract_feats(token),},})



 #################################################
 ##############################  Scriviamo output
        
with open('ordered.json', 'w', encoding='utf-8') as f:
    lemma_info = list(lemma_info.items())
    print('types = ', len(lemma_info))
    duplicate_dict = list(duplicate_dict.items())
    triplicate_dict = list(triplicate_dict.items())
    quadruplicate_dict = list(quadruplicate_dict.items())
    quintuplicate_dict = list(quintuplicate_dict.items())
    sext_dict = list(sext_dict.items())
    ept_dict = list(ept_dict.items())
    oct_dict = list(oct_dict.items())
    nine_dict = list(nine_dict.items())
    lemma_info.extend(duplicate_dict)
    lemma_info.extend(triplicate_dict)
    lemma_info.extend(quadruplicate_dict)
    lemma_info.extend(quintuplicate_dict)
    lemma_info.extend(sext_dict)
    lemma_info.extend(ept_dict)
    lemma_info.extend(oct_dict)
    lemma_info.extend(nine_dict)
    lemma_info.sort(key=lambda x: x[0].casefold())
    f.write('{\n')
    for i, (lemma, info) in enumerate(lemma_info):
        f.write(f'"{lemma}": {json.dumps(info)}')
        if i < len(lemma_info) - 1:
            f.write(',\n')
    f.write('\n}')

print ('sentences = ', sentencs)
print ('tokens = ', token_processed)
ambs = len(duplicate_dict)*2 + len(triplicate_dict) + len(quadruplicate_dict) + len (quintuplicate_dict) + len (sext_dict) + len (ept_dict) + len(oct_dict) + len(nine_dict)
lar = ambs/len(lemma_info) 
print (f'ambiguous tokens = {ambs}')
print (f'Lexical Ambiguity Ratio: {lar} ({ambs}/{len(lemma_info)})')


print (added_nine)

print ('backward_dependencies = ', backward_dep)
print ('local_back_dep = ', local_back_dep)
print ('local dep ratio = ', local_back_dep/backward_dep)
print ('dependencies = ', dependencies)

print ('final lexicon = ', len(lemma_info))


