import sys
import os


def call_llm(api_key):
    prompt = """

    """
    # call llm with api key
    return True if api_key else False


def verify_c_code(c_code: str) -> bool:
    # Placeholder for actual verification logic
    return True if c_code else False


def main():
    if len(sys.argv) != 3:
        print("Make sure code is highlighted and api key is entered")
        sys.exit(1)
    c_code = sys.argv[1]
    api_key = sys.argv[2]
    os.environ["OPENAI_API_KEY"] = api_key
    is_valid = verify_c_code(c_code)
    if is_valid:
        return '{"valid": true}'
    else:
        return '{"valid": false}'


if __name__ == "__main__":
    main()
