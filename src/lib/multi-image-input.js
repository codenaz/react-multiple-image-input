import React, { useState, useRef, useEffect } from 'react';
import PropTypes from 'prop-types';
import ReactCrop, {centerCrop, makeAspectCrop} from 'react-image-crop';
import { ThemeProvider } from 'styled-components';
import ImageIcon from './components/ImageIcon';
import ImageOverlay from './components/ImageOverlay';
import ImageBox from './components/ImageBox';
import ImageInput from './components/ImageInput';
import { Button } from './components/Button';
import Image from './components/Image';
import Text from './components/Text';
import Modal from './components/Modal';
import theme, { darkTheme, lightTheme } from './theme';
import { ImageOptionsWrapper } from './components/ImageOptions';
import DeleteIcon from './components/DeleteIcon';
import EditIcon from './components/EditIcon';
import 'react-image-crop/dist/ReactCrop.css';

export default function MultiImageInput({
  images: files,
  setImages: setFiles,
  cropConfig,
  max,
  allowCrop,
  ...props
}) {
  const [numberOfImages, setNumberOfImages] = useState(
    Object.keys(files).length < max ? Object.keys(files).length : max
  );

  const [originalFiles, setOriginalFiles] = useState(files);

  const [fileUploadRefs, setFileUploadRefs] = useState({});

  const [currentImage, setCurrentImage] = useState(null);

  const currentFile = useRef(null);

  const currentFileInputIndex = useRef(null);

  const [crop, setCrop] = useState(cropConfig.crop);

  let userTheme;

  if (typeof props.theme === 'string') {
    userTheme = props.theme === 'light' ? lightTheme : darkTheme;
  } else if (typeof props.theme === 'object') {
    userTheme = props.theme;
  }

  useEffect(() => {
    const fileUploadRefsCopy = {};

    Array(numberOfImages)
      .fill()
      .forEach((_, index) => {
        fileUploadRefsCopy[index] = React.createRef();
      });

    setFileUploadRefs(fileUploadRefsCopy);
  }, [numberOfImages]);

  useEffect(() => {
    let imageCount = Object.keys(files).length;
    if (imageCount < max) {
      setNumberOfImages(Object.keys(files).length + 1);
    } else {
      setNumberOfImages(Object.keys(files).length);
    }
  }, [files, max]);

  const handleFileChange = async (e, index) => {
    try {
      e.preventDefault();

      const maxAllowedImages = max - Object.keys(files).length;

      if (e.target.files.length > maxAllowedImages) {
        throw new Error(`You cannot upload more than ${max} ${max > 1 ? 'images' : 'image'}`)
      }

      const selectedFiles = Array.from(e.target.files);

      const imageURIs = await Promise.all(
        selectedFiles.map(f => {
          return new Promise((resolve, reject) => {
            const reader = new FileReader();

            reader.onloadend = () => {
              const image = document.createElement('img');

              const { minWidth, minHeight } = cropConfig;

              image.onload = () => {
                if (minWidth && image.width < minWidth) {
                  reject(
                    `Image width cannot be less than ${cropConfig.minWidth}px`
                  );
                }
                if (minHeight && image.width < minHeight) {
                  reject(
                    `Image height cannot be less than ${cropConfig.minWidth}px`
                  );
                }
                resolve(reader.result);
              };
              image.src = reader.result;
            };

            reader.onerror = e => {
              reject(e);
            };

            reader.readAsDataURL(f);
          });
        })
      );

      const imageUrisObject = {};

      for (let i = index; i < index + imageURIs.length; i++) {
        imageUrisObject[i] = imageURIs[i - index];
        currentFileInputIndex.current = i;
      }

      setFiles({ ...files, ...imageUrisObject });

      if (allowCrop) {
        setCurrentImage(imageUrisObject[index + imageURIs.length - 1]);
        setOriginalFiles({ ...originalFiles, ...imageUrisObject });
      }
    } catch (e) {
      if (props.handleError) {
        props.handleError(e);
      } else {
        alert(e);
      }
    }
  };

  const selectForCrop = (e, i) => {
    currentFileInputIndex.current = i;
    setCurrentImage(originalFiles[i]);
  };

  const onCropComplete = crop => {
    makeClientCrop(crop);
  };

  const onImageLoaded = image => {
    currentFile.current = image;
    if (crop.aspect) {
      const croppedImage = centerCrop(
        makeAspectCrop(
          {
            unit: '%',
            width: 100,
          },
          crop.aspect,
          image.naturalWidth,
          image.naturalHeight
        ),
        image.naturalWidth,
        image.naturalHeight
      )
      setCrop(croppedImage);
    }
  };

  const makeClientCrop = crop => {
    const imageRef = currentFile.current;
    if (imageRef && imageRef.width && imageRef.height) {
      const base64Image = getCroppedImage(imageRef, crop);

      setFiles({ ...files, [currentFileInputIndex.current]: base64Image });
    }
  };

  const getCroppedImage = (image, crop) => {
    const canvas = document.createElement('canvas');

    const scaleX = image.naturalWidth / image.width;

    const scaleY = image.naturalHeight / image.height;

    canvas.width = crop.width;

    canvas.height = crop.height;

    const ctx = canvas.getContext('2d');

    ctx.drawImage(
      image,
      crop.x * scaleX,
      crop.y * scaleY,
      crop.width * scaleY,
      crop.height * scaleY,
      0,
      0,
      crop.width,
      crop.height
    );

    const base64Image = canvas.toDataURL('image/jpeg');

    return base64Image;
  };

  const exitCrop = e => {
    if (e) {
      e.preventDefault();
    }
    setCurrentImage(null);
    currentFile.current = null;
    currentFileInputIndex.current = null;
  };

  const removeImage = (e, index) => {
    fileUploadRefs[index].current.value = '';

    const reIndexedFiles = {};
    const reIndexedOriginals = {};

    for (let i = index - 1; i >= 0; i--) {
      reIndexedFiles[i] = files[i];
      if (allowCrop) {
        reIndexedOriginals[i] = originalFiles[i];
      }
    }

    if (Object.keys(files).length === max) {
      for (let i = index; i < numberOfImages - 1; i++) {
        reIndexedFiles[i] = files[i + 1];

        if (allowCrop) {
          reIndexedOriginals[i] = originalFiles[i + 1];
        }
      }
    } else {
      for (let i = index; i < numberOfImages - 2; i++) {
        reIndexedFiles[i] = files[i + 1];

        if (allowCrop) {
          reIndexedOriginals[i] = originalFiles[i + 1];
        }
      }
    }

    setFiles(reIndexedFiles);

    if (allowCrop) {
      setOriginalFiles(reIndexedOriginals);
    }

    exitCrop();

    e.stopPropagation();
    return;
  };

  return (
    <ThemeProvider theme={{ ...theme, colors: userTheme }}>
      <ImageBox>
        {Array(numberOfImages)
          .fill()
          .map((_, index) => (
            <ImageInput key={index}>
              {files[index] ? (
                <>
                  <ImageOverlay>
                    <Image alt={`uploaded image${index}`} src={files[index]} />
                  </ImageOverlay>
                  <ImageOptionsWrapper>
                    <EditIcon
                      aria-label={`Edit Image ${index}`}
                      role="button"
                      onClick={e => selectForCrop(e, index)}
                    />
                    <DeleteIcon
                      aria-label={`Delete Image ${index}`}
                      role="button"
                      onClick={e => removeImage(e, index)}
                    />
                  </ImageOptionsWrapper>
                </>
              ) : (
                <div
                  role="button"
                  onClick={() => fileUploadRefs[index].current.click()}
                  style={{ cursor: 'pointer' }}
                >
                  <ImageIcon
                    fill={userTheme.outlineColor}
                    style={{ marginBottom: '0.5rem' }}
                    width={58}
                    height={46}
                  />
                  <Text
                    fontSize="small"
                    color="outlineColor"
                    style={{ display: 'block' }}
                  >
                    ADD IMAGE
                  </Text>
                </div>
              )}
              <input
                type="file"
                multiple
                onChange={e => handleFileChange(e, index)}
                ref={fileUploadRefs[index]}
                style={{ visibility: 'hidden' }}
                accept="image/*"
              />
            </ImageInput>
          ))}
      </ImageBox>

      {allowCrop && currentImage && (
        <Modal isOpen={true} toggle={exitCrop}>
          <Modal.Header>Crop Image</Modal.Header>
          <Modal.Body>
            <ReactCrop
              {...cropConfig}
              crop={crop}
              onChange={setCrop}
              onComplete={onCropComplete}
              src={currentImage}
            >
              <Image src={currentImage} onLoad={onImageLoaded} alt="Crop" />
            </ReactCrop>
          </Modal.Body>
          <Modal.Footer>
            <Button type="button" onClick={exitCrop} size="normal">
              Crop
            </Button>
          </Modal.Footer>
        </Modal>
      )}
    </ThemeProvider>
  );
}

MultiImageInput.defaultProps = {
  max: 3,
  theme: 'dark',
  allowCrop: true,
  cropConfig: {
    maxWidth: 800,
    minWidth: 300,
    crop: {},
    ruleOfThirds: true,
    aspect: 4 / 3
  }
};

MultiImageInput.propTypes = {
  images: PropTypes.object.isRequired,
  setImages: PropTypes.func.isRequired,
  allowCrop: PropTypes.bool,
  max: PropTypes.number,
  theme: PropTypes.oneOfType([PropTypes.object, PropTypes.string]),
  cropConfig: PropTypes.object,
  handleError: PropTypes.func
};
