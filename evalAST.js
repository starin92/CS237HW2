F.evalAST = function(ast) {
  var env = [null,null,null];
  return ev(env,ast);
};

function ev(env, ast) {
  if (typeof ast === "number" || typeof ast === "boolean" || typeof ast === "string" || ast === null) {
    return ast;
  } else {
    var tag = ast[0];
    switch (tag) {
        case "+":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");
          return a1 + a2;
        case "-":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");
          return a1 - a2;
        case "*":          
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");
          return a1 * a2;
        case "/":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");        
          return a1 / a2;
        case "%":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");        
          return a1 % a2;
        case "=":
          return ev(env,ast[1]) === ev(env,ast[2]);
        case "!=":
          return ev(env,ast[1]) !== ev(env,ast[2]);
        case "<":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");        
          return a1 < a2;
        case ">":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"number");        
          return a1 > a2;
        case "and":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"boolean");          
          return a1 && a2;
        case "or":
          var a1 = ev(env,ast[1]);
          var a2 = ev(env,ast[2]);
          checkArgs(a1,a2,"boolean");        
          return a1 || a2;
        case "if":
          var cond = ev(env,ast[1]);
          if(typeof cond !== "boolean"){
            throw new Error("if requires boolean");
          }
          return cond ? ev(env,ast[2]) : ev(env,ast[3]);
        case "id":
          var c_env=env;
          while(c_env[2]!==null){
            if(c_env[0]===ast[1]){
              return c_env[1]; 
            }
            c_env=c_env[2];
          }
          throw new Error("undeclared id:"+ast[1]);
        case "let":
          var id=ev(env,ast[1]);
          var val=ev(env,ast[2]);
          var newenv = [id,val,env];
          return ev(newenv,ast[3]);
        case "fun":
          var args=ast[1];
          var body=ast[2];
          return ["closure",args,body,env];
        case "call":
          var f=ev(env,ast[1]);
          if(f[0]!=="closure"){
            throw new Error("call on non-function type");
          }
          var args = ast.slice(2);
          if(f[1].length!==args.length){
            throw new Error("wrong number of arguments");
          } 
          //make env = arguments env -> closure env
          var newenv=f[3];
          var aval;
          for(var i=0;i<args.length;i++){
            aval=ev(env,args[i]);
            newenv=[f[1][i],aval,newenv];
          }
          return ev(newenv,f[2]);
        case "cons":
          return ["cons",ev(env,ast[1]),ev(env,ast[2])];
        case "seq":
          ev(env,ast[1]);
          return ev(env,ast[2]);
        case "match":
          var p=ev(env,ast[1]);
          var patterns = ast.slice(2);
          for(var i=0;i<patterns.length;i+=2){
            var newenv = matchRec(env,p,patterns[i]);
            if(newenv==="no") continue;
            return ev(newenv,patterns[i+1]);
          }
          throw new Error("match failure");
        case "set":
          var c_env=env;
          while(c_env[2]!==null){
            if(c_env[0]===ast[1]){
              return c_env[1]; 
            }
            c_env=c_env[2];
          }
          throw new Error("set on undeclared id:"+ast[1]);
           
    }
  }
}

function checkArgs(ast1,ast2,type){
  if(typeof ast1 !== type || typeof ast2 !== type){
    throw new Error("incorrect type to operator");
  }
  return;
}

function matchRec(env,matchExpr,pattern){
  if(pattern===null){
    if(matchExpr!==null){
      return "no";
    } else {
      return env;
    }
  } else if(typeof pattern === "number" || typeof pattern === "boolean"){
    if(matchExpr===pattern){
      return env;
    } else {
      return "no";
    }
  } else if(pattern[0]==="_"){
    if(typeof matchExpr ==="number" || typeof matchExpr ==="boolean"){
      return env;
    } else {
      return "no";
    }
  } else if(pattern[0]==="id") {
    if(typeof matchExpr ==="number" || typeof matchExpr ==="boolean"){
      return [pattern[1], matchExpr, env];
    } else {
      return "no";
    }
  } else if(pattern[0]==="cons"){
    if(matchExpr[0]!=="cons"){
      return "no";
    } else {
      var r1,r2;
      r1=matchRec(env,matchExpr[1],pattern[1]);
      if(r1==="no"){
        return "no";
      }
      r2=matchRec(r1,matchExpr[2],pattern[2]);
      return r2;
    }
  }
}
