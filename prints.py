message = ''
for x in range(30, 40):
    message += "rule"+str(x)+", "
print(message)

message = ''
for x in range(30, 40):
    message += "auxRule3 == rule"+str(x)+", "
print(message)
