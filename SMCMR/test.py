import torch

if __name__ == "__main__":
    a = torch.zeros(5)
    print(a)
    # c = torch.tensor([0.1,0.2,0.3,0.2])
    b = torch.argmax(a)
    print(b)