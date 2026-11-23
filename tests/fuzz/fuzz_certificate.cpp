// Fuzz target: the certificate reader and the reference checker must never
// crash, hang or invoke undefined behaviour, whatever the input.
//
// Built with -fsanitize=fuzzer (ZS_BUILD_FUZZERS, clang) it is a libFuzzer
// target; built with ZS_FUZZ_REPLAY it is a program that feeds every file
// given on the command line (or found in the directories given) through the
// same entry point, which CTest runs on the seed corpus on every platform.
#include <zeno/certificate.hpp>

#include <cstddef>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <string>

extern "C" int LLVMFuzzerTestOneInput(const std::uint8_t* data, std::size_t size)
{
    std::istringstream in(std::string(reinterpret_cast<const char*>(data), size));
    zeno::Certificate cert;
    try
    {
        cert = zeno::readCertificate(in);
    }
    catch(const std::runtime_error&)
    {
        return 0; // rejected input: fine
    }
    // Keep each run fast: the checker's cost grows with the instance.
    const auto& i = cert.instance;
    if(i.d.size() > 8 || i.t > 12 || i.p > 12 || cert.front.size() > 64)
        return 0;
    for(const auto* v : {&i.d, &i.dbar})
        for(auto x : *v)
            if(x > 10'000)
                return 0;
    for(const auto& point : cert.front)
        if(point.makespan > 1'000'000)
            return 0;
    try
    {
        (void)zeno::checkCertificate(cert);
    }
    catch(const std::invalid_argument&)
    {
        // Reported as an invalid instance by the library: fine.
    }
    return 0;
}

#ifdef ZS_FUZZ_REPLAY
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <vector>

int main(int argc, char** argv)
{
    std::size_t files = 0;
    const auto run = [&](const std::filesystem::path& path) {
        std::ifstream file(path, std::ios::binary);
        const std::vector<char> bytes{std::istreambuf_iterator<char>(file), std::istreambuf_iterator<char>()};
        LLVMFuzzerTestOneInput(reinterpret_cast<const std::uint8_t*>(bytes.data()), bytes.size());
        ++files;
    };
    for(int a = 1; a < argc; ++a)
    {
        const std::filesystem::path root(argv[a]);
        if(std::filesystem::is_directory(root))
        {
            for(const auto& entry : std::filesystem::recursive_directory_iterator(root))
                if(entry.is_regular_file())
                    run(entry.path());
        }
        else
            run(root);
    }
    std::cout << "fuzz-certificate replay: " << files << " inputs\n";
    return files > 0 ? 0 : 1;
}
#endif
