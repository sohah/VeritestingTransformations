package gov.nasa.jpf.symbc.veritesting;

/*
Copyright 2011 Karl-Michael Schneider

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/
//package org.jwatter.util;
//http://www.java2s.com/Code/Java/Reflection/Methodsignature.htm
import com.ibm.wala.types.TypeName;
import org.apache.bcel.classfile.Utility;

import java.io.File;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;

public class ReflectUtil
{
    public static String getSignature ( Method method )
    {
        return method.getName() + "("
                + parametersAsString(method) + ")"
                + Utility.getSignature(method.getReturnType().getSimpleName());
    }
    public static String parametersAsString ( Method method )
    {
        Class<?>[] parameterTypes = method.getParameterTypes();
        if ( parameterTypes.length == 0 ) return "";
        StringBuilder paramString = new StringBuilder();

        for ( int i = 0 ; i < parameterTypes.length ; i++ )
        {
            paramString.append(Utility.getSignature(parameterTypes[i].getSimpleName()));
        }
        return paramString.toString();
    }

    /*public static String getSignature(String classPath, String currentClassName, String methodPartialName) {
        //https://docs.oracle.com/javase/tutorial/reflect/member/methodType.html
        try {
            File f = new File(classPath);
            URL[] cp = {f.toURI().toURL()};
            URLClassLoader urlcl = new URLClassLoader(cp);
            Class c = urlcl.loadClass(currentClassName);
            Method[] allMethods = c.getDeclaredMethods();
            for (Method m : allMethods) {
                String signature = getSignature(m);
                if(signature.contains(methodPartialName)) return signature;
            }

            // production code should handle these exceptions more gracefully
        } catch (ClassNotFoundException x) {
            x.printStackTrace();
        } catch (MalformedURLException e) {
            e.printStackTrace();
        }
        return null;
    }*/
}
