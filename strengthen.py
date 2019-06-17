#------------------------------Importing libraries---------------------------------------

import re
import fileinput 
from collections import defaultdict

#-----------------------------------------done--------------------------------------------


#-------------Read the program to be converted in to more efficient program---------------
path=input("Give path to your program:")
with open(path, 'r') as fin:
    content=(fin.readlines())


file=open("modified_program.txt","w")
file.writelines(content)
file.close()
with open("modified_program.txt", 'r') as fdin:
    new_content=(fdin.readlines())

print("new_content",new_content)

#-----------------------------------------done--------------------------------------------


#------------------------------------Making of V starts-----------------------------------
pattern='var '
V=dict()
list_int=[]
list_bool=[]
for line in new_content:
	if pattern in line:
		for entry in (line.split(" ")):
			if "int" in entry:
				list_int.append(entry[:entry.find(':')])
			elif("bool" in entry):
				list_bool.append(entry[:entry.find(':')])
V["int"]=list_int
V["bool"]=list_bool			
print("V is:",format(V))


#-------------------------------------Making of V ends------------------------------------

#----------------------Finding out the lines to be replaced --starts----------------------
dec=[]
call=[]
for line in new_content:
	if "Invariant" in line:	
		if((line[line.find(")")+1])==":"):
			dec.append(line[line.find("(")+1:line.find(")")])
		else:
			call.append(line[line.find("(")+1:line.find(")")])
call=call[0]
dec=dec[0]		

#----------------------Finding out the lines to be replaced --ends------------------------



#--------------------Finding out the variables to be removed --starts---------------------
v_remove=[] #list of variables to remove from V
for datatype in V:
	for variable in V[datatype]:
		if(variable.find("_")!=-1):
			v_remove.append(variable)
print("variables to be removed: ",v_remove)
v_remove=set(v_remove)

#----------------------Finding out the variables to be removed --ends---------------------	



#--------------Making of string to be replaced at calling of function--starts-------------	

call_list=call.split(",")
to_replace_call=list(filter(lambda x: x not in v_remove,call_list))
print("to_replace_call",to_replace_call)
to_replace_call_str=",".join(to_replace_call)

#--------------Making of string to be replaced at calling of function--ends---------------	





#----------Making of string to be replaced at declaration of function--starts-------------	

reverse_V=defaultdict()
for item in V:
	for x in V[item]:
		reverse_V[x]=item
		
print("reverse dictionary:", reverse_V)

dec_replace_dic={x:reverse_V[x] for x in to_replace_call}
print("reknk",dec_replace_dic)

dec_replace_list=[]
for item in dec_replace_dic:
	dec_replace_list.append(item+":"+dec_replace_dic[item])
print(dec_replace_list)
dec_replace_str=",".join(dec_replace_list)
print(dec_replace_str)


#-----------Making of string to be replaced at declaration of function--ends--------------	





#-----------------------------Replacing the respective lines -----------------------------		

with fileinput.FileInput("modified_program.txt", inplace=True) as file:
    for line in file:
        print(line.replace(call, to_replace_call_str), end='')
        
        
with fileinput.FileInput("modified_program.txt", inplace=True) as file:
    for line in file:
        print(line.replace(dec, dec_replace_str), end='')
        
#-----------------------------------------done--------------------------------------------
