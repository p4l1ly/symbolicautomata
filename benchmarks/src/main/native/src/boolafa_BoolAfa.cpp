#include <jni.h>
#include <iostream>

#include <automata-safa-capnp/SeparatedAfa.capnp.h>
#include <automata-safa-capnp/SeparatedAfaRpc.capnp.h>
#include <capnp/message.h>
#include <capnp/serialize-packed.h>
#include <capnp/ez-rpc.h>

#include "boolafa_BoolAfa.h"

namespace schema = automata_safa_capnp::separated_afa;
namespace rpcschema = automata_safa_capnp::separated_afa_rpc;

class LoadedModelImpl final: public rpcschema::LoadedModel::Server {
public:
    kj::Promise<void> solve(SolveContext context) override {
        std::cout << "solve" << std::endl;
        context.getResults().setEmpty(true);
        return kj::READY_NOW;
    }
};

class LoaderImpl final: public rpcschema::Loader::Server {
public:
    kj::Promise<void> load(LoadContext context) override {
        std::cout << "load" << std::endl;
        schema::SeparatedAfa::Reader cnfafa = context.getParams().getModel();
        context.getResults().setLoadedModel(kj::heap<LoadedModelImpl>());
        return kj::READY_NOW;
    }
};

JNIEXPORT void JNICALL Java_boolafa_BoolAfa_runRpcServer(JNIEnv *, jobject) {
    capnp::EzRpcServer server(kj::heap<LoaderImpl>(), "0.0.0.0", 4000);
    auto& waitScope = server.getWaitScope();
    kj::NEVER_DONE.wait(waitScope);
}
