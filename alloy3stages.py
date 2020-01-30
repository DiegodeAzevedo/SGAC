import subprocess
import time
import os

timeAInit = time.time()
p = subprocess.Popen("cd C:"+os.sep+"Users"+os.sep+"dead1401"+os.sep+"Documents"+os.sep+"alloy"+os.sep+
                     "tool & java -Xss4m -cp \".;alloy4.2_2015-02-22.jar\" ExampleUsingTheCompiler "+
                     "sgac_core.als "+
                     "sgac_core1.als "+
                     "sgac_core2.als ",
                     stdout=subprocess.PIPE,
                     stderr=subprocess.PIPE,
                     shell=True)
output, errors = p.communicate()
n = ""
timeAComulative = time.time() - timeAInit
if True:
    if p.returncode==0:
        print("Alloy Analyzer executed successfully ("+n+")")
        print(output)
    else:
        print("Alloy Analyzer - error reported in "+n+" and the return code is "+str(p.returncode))
        print(errors)
print(timeAComulative)