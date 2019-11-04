message = ''
for x in range(30, 40):
    message += "rule"+str(x)+", "
print(message)

message = ''
for x in range(0, 22):
    message += "SE(E3=Sheet2!$A$"+str(x+2)+",Sheet2!$E$"+str(x+2)+","
print(message)

PythonSubGraph = dict()
